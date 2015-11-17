/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Concrete values = constants of different types.
 * This is used to build models: a model is a mapping from terms to concrete values.
 */

#include <inttypes.h>

#include "model/concrete_values.h"
#include "terms/bv64_constants.h"
#include "utils/hash_functions.h"
#include "utils/int_array_sort.h"
#include "utils/memalloc.h"





/*****************************************
 *  TABLE INITIALIZATION/DELETION/RESET  *
 ****************************************/

/*
 * Initialize a table;
 * - n = initial size. If n is zero, the default size is used.
 * - ttbl = attached type table.
 */
void init_value_table(value_table_t *table, uint32_t n, type_table_t *ttbl) {
  if (n == 0) {
    n = DEF_VALUE_TABLE_SIZE;
  }
  if (n >= MAX_VALUE_TABLE_SIZE) {
    out_of_memory();
  }

  table->size = n;
  table->nobjects = 0;
  table->kind = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  table->desc = (value_desc_t *) safe_malloc(n * sizeof(value_desc_t));
  table->canonical = allocate_bitvector0(n);

  table->type_table = ttbl;
  init_int_htbl(&table->htbl, 0);
  init_bvconstant(&table->buffer);

  table->unknown_value = null_value;
  table->true_value = null_value;
  table->false_value = null_value;
  table->first_tmp = -1; // no temporary objects
}


/*
 * Make the table larger (by 50%)
 */
static void extend_value_table(value_table_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  assert(n > table->size);

  if (n >= MAX_VALUE_TABLE_SIZE) {
    out_of_memory();
  }

  table->size = n;
  table->kind = (uint8_t *) safe_realloc(table->kind, n * sizeof(uint8_t));
  table->desc = (value_desc_t *) safe_realloc(table->desc, n * sizeof(value_desc_t));
  table->canonical = extend_bitvector0(table->canonical, n, table->size);
}


/*
 * Allocate a new object index
 * - kind and descriptor are not initialized
 */
static value_t allocate_object(value_table_t *table) {
  value_t i;

  i = table->nobjects;
  if (i == table->size) {
    extend_value_table(table);
  }
  assert(i < table->size);
  table->nobjects = i+1;
  return i;
}



/*
 * Delete descriptors for objects k ... nobjects - 1
 */
static void vtbl_delete_descriptors(value_table_t *table, uint32_t k) {
  uint32_t i, n;

  n = table->nobjects;
  table->nobjects = k;

  assert(k <= n);
  for (i=k; i<n; i++) {
    switch (table->kind[i]) {
    case UNKNOWN_VALUE:
    case BOOLEAN_VALUE:
      break;
    case RATIONAL_VALUE:
      q_clear(&table->desc[i].rational);
      break;
    case BITVECTOR_VALUE:
      safe_free(table->desc[i].ptr);
      break;
    }
  }
}


/*
 * Reset the table:
 * - delete all descriptors
 * - empty the table.
 */
void reset_value_table(value_table_t *table) {
  vtbl_delete_descriptors(table, 0);
  reset_int_htbl(&table->htbl);

  table->nobjects = 0;
  table->unknown_value = null_value;
  table->true_value = null_value;
  table->false_value = null_value;
  table->first_tmp = -1;
}


/*
 * Delete the table
 */
void delete_value_table(value_table_t *table) {
  vtbl_delete_descriptors(table, 0);
  safe_free(table->kind);
  safe_free(table->desc);
  delete_bitvector(table->canonical);
  delete_int_htbl(&table->htbl);
  table->kind = NULL;
  table->desc = NULL;
  table->canonical = NULL;
}





/******************************************************
 *  CONSTRUCTORS: VALUES THAT DON'T USE HASH CONSING  *
 *****************************************************/

/*
 * Unknown value: for undefined stuff
 */
value_t vtbl_mk_unknown(value_table_t *table) {
  value_t i;

  i = table->unknown_value;
  if (i < 0) {
    i = allocate_object(table);
    table->kind[i] = UNKNOWN_VALUE;
    table->desc[i].ptr = NULL;
    table->unknown_value = i;
    set_bit(table->canonical, i);
  }
  return i;
}


/*
 * True and false
 */
value_t vtbl_mk_true(value_table_t *table) {
  value_t i;

  i = table->true_value;
  if (i < 0) {
    i = allocate_object(table);
    table->kind[i] = BOOLEAN_VALUE;
    table->desc[i].integer = 1; // non-zero means true
    table->true_value = i;
    set_bit(table->canonical, i);
  }
  return i;
}

value_t vtbl_mk_false(value_table_t *table) {
  value_t i;

  i = table->false_value;
  if (i < 0) {
    i = allocate_object(table);
    table->kind[i] = BOOLEAN_VALUE;
    table->desc[i].integer = 0; // zero means false
    table->false_value = i;
    set_bit(table->canonical, i);
  }
  return i;
}


/*
 * Booleans: val = 0 means false, val != 0 means true
 */
value_t vtbl_mk_bool(value_table_t *table, int32_t val) {
  if (val) {
    return vtbl_mk_true(table);
  } else {
    return vtbl_mk_false(table);
  }
}


/*
 * Negation of v
 */
value_t vtbl_mk_not(value_table_t *table, value_t v) {
  assert(v >= 0 && (v == table->true_value || v == table->false_value));

  if (v == table->true_value) {
    return vtbl_mk_false(table);
  } else {
    return vtbl_mk_true(table);
  }
}



/********************
 *   HASH CONSING   *
 *******************/

/*
 * There's a hobj for rationals, unint, bitvectors, tuples, and map objects.
 * Each hobj structure starts with a function descriptor m
 * with three fields:
 *   m.hash = compute hash code
 *   m.eq = check equality
 *   m.build = build a fresh value
 */
typedef struct {
  int_hobj_t m;
  value_table_t *table;
  rational_t *v;
} rational_hobj_t;

typedef struct {
  int_hobj_t m;
  value_table_t *table;
  uint32_t nbits;
  uint32_t *data;  // must be normalized modulo (2^nbits)
} bv_hobj_t;


/*
 * Hash functions
 */
static uint32_t hash_rational_value(rational_hobj_t *o) {
  uint32_t h_num, h_den;
  q_hash_decompose(o->v, &h_num, &h_den);
  return jenkins_hash_mix2(h_num, h_den);
}

static uint32_t hash_bv_value(bv_hobj_t *o) {
  return bvconst_hash(o->data, o->nbits);
}


/*
 * Equality testing: compare the object being constructed with
 * an existing value of index i in the table.
 */
static bool equal_rational_value(rational_hobj_t *o, value_t i) {
  value_table_t *table;

  table = o->table;
  return table->kind[i] == RATIONAL_VALUE && q_eq(&table->desc[i].rational, o->v);
}

static bool equal_bv_value(bv_hobj_t *o, value_t i) {
  value_table_t *table;
  value_bv_t *d;

  table = o->table;
  if (table->kind[i] != BITVECTOR_VALUE) {
    return false;
  }
  d = table->desc[i].ptr;
  return d->nbits == o->nbits && bvconst_eq(d->data, o->data, d->width);
}


/*
 * Constructors
 */
static value_t build_rational_value(rational_hobj_t *o) {
  value_table_t *table;
  value_t i;

  table = o->table;
  i = allocate_object(table);
  table->kind[i] = RATIONAL_VALUE;
  q_init(&table->desc[i].rational);
  q_set(&table->desc[i].rational, o->v);
  set_bit(table->canonical, i);

  return i;
}

static value_t build_bv_value(bv_hobj_t *o) {
  value_table_t *table;
  value_bv_t *d;
  uint32_t w;
  value_t i;

  w = (o->nbits + 31) >> 5; // ceil(nbits/32)
  d = (value_bv_t *) safe_malloc(sizeof(value_bv_t) + w * sizeof(uint32_t));
  d->nbits = o->nbits;
  d->width = w;
  bvconst_set(d->data, w, o->data);

  table = o->table;
  i = allocate_object(table);
  table->kind[i] = BITVECTOR_VALUE;
  table->desc[i].ptr = d;
  set_bit(table->canonical, i);

  return i;
}


/*
 * Return a rational constant = v
 */
value_t vtbl_mk_rational(value_table_t *table, rational_t *v) {
  rational_hobj_t hobj;

  hobj.m.hash = (hobj_hash_t) hash_rational_value;
  hobj.m.eq =  (hobj_eq_t) equal_rational_value;
  hobj.m.build = (hobj_build_t) build_rational_value;
  hobj.table = table;
  hobj.v = v;

  return int_htbl_get_obj(&table->htbl, &hobj.m);
}

/*
 * Return a rational constant equal to i
 */
value_t vtbl_mk_int32(value_table_t *table, int32_t i) {
  rational_hobj_t hobj;
  rational_t aux;
  value_t k;

  q_init(&aux);
  q_set32(&aux, i);
  hobj.m.hash = (hobj_hash_t) hash_rational_value;
  hobj.m.eq =  (hobj_eq_t) equal_rational_value;
  hobj.m.build = (hobj_build_t) build_rational_value;
  hobj.table = table;
  hobj.v = &aux;

  k = int_htbl_get_obj(&table->htbl, &hobj.m);
  q_clear(&aux);

  return k;
}


/*
 * Bit vector constant: defined by array a:
 * - a[i] = 0 means bit[i] = 0
 * - a[i] != 0 means bit[i] = 1
 */
value_t vtbl_mk_bv(value_table_t *table, uint32_t n, int32_t *a) {
  bv_hobj_t hobj;
  bvconstant_t *b;

  // copy the constant in table's buffer
  b = &table->buffer;
  bvconstant_set_bitsize(b, n);
  bvconst_set_array(b->data, a, n);
  bvconst_normalize(b->data, n);

  // hash-consing
  hobj.m.hash = (hobj_hash_t) hash_bv_value;
  hobj.m.eq = (hobj_eq_t) equal_bv_value;
  hobj.m.build = (hobj_build_t) build_bv_value;
  hobj.table = table;
  hobj.nbits = n;
  hobj.data = b->data;

  return int_htbl_get_obj(&table->htbl, &hobj.m);
}


/*
 * Bit vector constant defined by an array of words
 * - n = number of bits
 * - a = array of w words (w = ceil(n/32)
 */
value_t vtbl_mk_bv_from_bv(value_table_t *table, uint32_t n, uint32_t *a) {
  bv_hobj_t hobj;

  bvconst_normalize(a, n);  

  hobj.m.hash = (hobj_hash_t) hash_bv_value;
  hobj.m.eq = (hobj_eq_t) equal_bv_value;
  hobj.m.build = (hobj_build_t) build_bv_value;
  hobj.table = table;
  hobj.nbits = n;
  hobj.data = a;

  return int_htbl_get_obj(&table->htbl, &hobj.m);
}


/*
 * Bit vector constant defined by a bvconstant_t object
 * - b->bitsize = number of bits
 * - b->data = array of 32bit words
 */
value_t vtbl_mk_bv_from_constant(value_table_t *table, bvconstant_t *b) {
  return vtbl_mk_bv_from_bv(table, b->bitsize, b->data);
}


/*
 * Bit vector constant defined by a 64bit integer c
 * - n = number of bits to use
 */
value_t vtbl_mk_bv_from_bv64(value_table_t *table, uint32_t n, uint64_t c) {
  uint32_t aux[2];

  aux[0] = (uint32_t) c;
  aux[1] = (uint32_t) (c >> 32);
  return vtbl_mk_bv_from_bv(table, n, aux);
}


/*
 * Bitvector constant with all bits 0
 * - n = number of bits
 */
value_t vtbl_mk_bv_zero(value_table_t *table, uint32_t n) {
  bv_hobj_t hobj;
  bvconstant_t *b;

  assert(n > 0);

  // store 0b000...0 in the buffer
  b = &table->buffer;
  bvconstant_set_all_zero(b, n);

  hobj.m.hash = (hobj_hash_t) hash_bv_value;
  hobj.m.eq = (hobj_eq_t) equal_bv_value;
  hobj.m.build = (hobj_build_t) build_bv_value;
  hobj.table = table;
  hobj.nbits = n;
  hobj.data = b->data;

  return int_htbl_get_obj(&table->htbl, &hobj.m);
}


/*
 * Bitvector constant with all bits 0, except the low-order bit
 * - n = number of bits
 */
value_t vtbl_mk_bv_one(value_table_t *table, uint32_t n) {
  bv_hobj_t hobj;
  bvconstant_t *b;

  assert(n > 0);

  // store 0b000..01 in the buffer
  b = &table->buffer;
  bvconstant_set_all_zero(b, n);
  bvconst_set_bit(b->data, 0);

  hobj.m.hash = (hobj_hash_t) hash_bv_value;
  hobj.m.eq = (hobj_eq_t) equal_bv_value;
  hobj.m.build = (hobj_build_t) build_bv_value;
  hobj.table = table;
  hobj.nbits = n;
  hobj.data = b->data;

  return int_htbl_get_obj(&table->htbl, &hobj.m);
}




/*
 * Return some value of type tau
 */
value_t vtbl_make_object(value_table_t *vtbl, type_t tau) {
  type_table_t *types;
  value_t v;

  types = vtbl->type_table;

  switch (type_kind(types, tau)) {
  case BOOL_TYPE:
    v = vtbl_mk_false(vtbl);
    break;

  case BITVECTOR_TYPE:
    v = vtbl_mk_bv_zero(vtbl, bv_type_size(types, tau));
    break;

  default:
    assert(false);
    v = vtbl_mk_unknown(vtbl);
    break;
  }

  return v;
}


/*
 * Attempt to construct two distinct objects of type tau.
 * - return true if that succeeds, false if tau is a singleton type
 * - store the two objects in a[0] and a[1]
 */
bool vtbl_make_two_objects(value_table_t *vtbl, type_t tau, value_t a[2]) {
  type_table_t *types;

  types = vtbl->type_table;

  switch (type_kind(types, tau)) {
  case BOOL_TYPE:
    a[0] = vtbl_mk_false(vtbl);
    a[1] = vtbl_mk_true(vtbl);
    break;

  case BITVECTOR_TYPE:
    a[0] = vtbl_mk_bv_zero(vtbl, bv_type_size(types, tau));
    a[1] = vtbl_mk_bv_one(vtbl, bv_type_size(types, tau));
    break;

  default:
    assert(false);
    return false;
  }

  return true;
}




/**************************************
 *  TEST WHETHER OBJECTS ARE PRESENT  *
 *************************************/

/*
 * Check whether a rational or integer constant is in the table
 * - return the object if found, -1 (i.e., null_value otherwise)
 */
value_t vtbl_find_rational(value_table_t *table, rational_t *v) {
  rational_hobj_t hobj;

  hobj.m.hash = (hobj_hash_t) hash_rational_value;
  hobj.m.eq =  (hobj_eq_t) equal_rational_value;
  hobj.m.build = (hobj_build_t) build_rational_value;
  hobj.table = table;
  hobj.v = v;

  return int_htbl_find_obj(&table->htbl, &hobj.m);
}

value_t vtbl_find_int32(value_table_t *table, int32_t x) {
  rational_hobj_t hobj;
  rational_t aux;
  value_t k;

  q_init(&aux);
  q_set32(&aux, x);
  hobj.m.hash = (hobj_hash_t) hash_rational_value;
  hobj.m.eq =  (hobj_eq_t) equal_rational_value;
  hobj.m.build = (hobj_build_t) build_rational_value;
  hobj.table = table;
  hobj.v = &aux;

  k = int_htbl_find_obj(&table->htbl, &hobj.m);
  q_clear(&aux);

  return k;
}


/*
 * Check presence of a bitvector constant defined by array of n integers:
 * - bit i is 0 if a[i] == 0
 * - bit i is 1 otherwise
 * - n = number of bits (must be positive).
 */
value_t vtbl_find_bv(value_table_t *table, uint32_t n, int32_t *a) {
  bv_hobj_t hobj;
  bvconstant_t *b;

  // copy the constant in table's buffer
  b = &table->buffer;
  bvconstant_set_bitsize(b, n);
  bvconst_set_array(b->data, a, n);
  bvconst_normalize(b->data, n);

  // hash-consing
  hobj.m.hash = (hobj_hash_t) hash_bv_value;
  hobj.m.eq = (hobj_eq_t) equal_bv_value;
  hobj.m.build = (hobj_build_t) build_bv_value;
  hobj.table = table;
  hobj.nbits = n;
  hobj.data = b->data;

  return int_htbl_find_obj(&table->htbl, &hobj.m);
}

/*
 * Same thing for the bitvector defined by c:
 * - n = number of bits (must be <= 64)
 */
value_t vtbl_find_bv64(value_table_t *table, uint32_t n, uint64_t c) {
  bv_hobj_t hobj;
  uint32_t aux[2];

  c = norm64(c, n);
  aux[0] = (uint32_t) c;
  aux[1] = (uint32_t) (c >> 32);

  hobj.m.hash = (hobj_hash_t) hash_bv_value;
  hobj.m.eq = (hobj_eq_t) equal_bv_value;
  hobj.m.build = (hobj_build_t) build_bv_value;
  hobj.table = table;
  hobj.nbits = n;
  hobj.data = aux;

  return int_htbl_find_obj(&table->htbl, &hobj.m);
}

/*
 * Same thing for the bitvector constant defined by b
 */
value_t vtbl_find_bvconstant(value_table_t *table, bvconstant_t *b) {
  bv_hobj_t hobj;
  uint32_t n;

  n = b->bitsize;
  bvconst_normalize(b->data, n);

  hobj.m.hash = (hobj_hash_t) hash_bv_value;
  hobj.m.eq = (hobj_eq_t) equal_bv_value;
  hobj.m.build = (hobj_build_t) build_bv_value;
  hobj.table = table;
  hobj.nbits = n;
  hobj.data = b->data;

  return int_htbl_find_obj(&table->htbl, &hobj.m);
}



/**********************************
 *  ENUMERATION OF FINITE TYPES   *
 *********************************/

/*
 * Bitvector: index i, size n
 */
static value_t vtbl_gen_bitvector(value_table_t *table, uint32_t n, uint32_t i) {
  bvconstant_t *b;

  b = &table->buffer;
  bvconstant_copy64(b, n, (uint64_t) i);
  return vtbl_mk_bv_from_constant(table, b);
}


/*
 * If tau is a finite type, then we can enumerate its elements from
 * 0 to card(tau) - 1. The following function construct and element
 * of finite type tau given an enumeration index i.
 * - tau must be finite
 * - i must be smaller than card(tau)
 */
value_t vtbl_gen_object(value_table_t *table, type_t tau, uint32_t i) {
  type_table_t *types;
  value_t v;

  types = table->type_table;
  assert(is_finite_type(types, tau) && i < type_card(types, tau));

  switch (type_kind(types, tau)) {
  case BOOL_TYPE:
    assert(i == 0 || i == 1);
    v = vtbl_mk_bool(table, i);
    break;

  case BITVECTOR_TYPE:
    v = vtbl_gen_bitvector(table, bv_type_size(types, tau), i);
    break;

  default:
    assert(false); // can't be a finite type
    v = null_value;
    break;
  }

  return v;
}


/*
 * TEST EXISTENCE OF OBJECTS USING THEIR INDEX
 */

/*
 * Check whether object of type tau and index i is present in table.
 * - tau must be finite
 * - i must be smaller than card(tau)
 * - return the object of index i if present, null_value otherwise
 */
value_t vtbl_find_object(value_table_t *table, type_t tau, uint32_t i) {
  type_table_t *types;

  types = table->type_table;
  assert(is_finite_type(types, tau) && i < type_card(types, tau));

  switch (type_kind(types, tau)) {
  case BOOL_TYPE:
    assert(i == 0 || i == 1);
    return vtbl_mk_bool(table, i);

  case BITVECTOR_TYPE:
    return vtbl_find_bv64(table, bv_type_size(types, tau), (uint64_t) i);

  default:
    assert(false);
    return null_value;
  }
}






/***********************
 *  TEMPORARY OBJECTS  *
 **********************/

/*
 * Mark all current objects as permanent.
 * All objects created after this function is called are temporary
 * and can be deleted by calling 'value_table_delete_tmp'.
 */
void value_table_start_tmp(value_table_t *table) {
  assert(table->first_tmp == -1);
  // make sure unknown, true, and false are constructed
  (void) vtbl_mk_unknown(table);
  (void) vtbl_mk_true(table);
  (void) vtbl_mk_false(table);

  // set the tmp mark
  table->first_tmp = table->nobjects;
}



/*
 * Delete all temporary objects.
 * They are stored at indices [first_tmp ... nobjects-1].
 * Do nothing if first_tmp is -1.
 * Reset first_tmp to -1.
 */
void value_table_end_tmp(value_table_t *table) {
  if (table->first_tmp >= 0) {
    vtbl_delete_descriptors(table, table->first_tmp);
    table->first_tmp = -1;
  }
}




/****************
 *  EVALUATION  *
 ***************/

/*
 * Evaluate (eq a b)
 */
value_t vtbl_eval_eq(value_table_t *table, value_t a, value_t b) {
  value_t v;

  assert(good_object(table, a) && good_object(table, b));

  if (a == b) {
    v = vtbl_mk_true(table);
  } else if (object_is_canonical(table, a) || object_is_canonical(table, b)) {
    v = vtbl_mk_false(table);
  } else {
    /*
     * a and b are non canonical
     */
    v = vtbl_mk_unknown(table);
  }

  return v;
}


/*
 * Check whether arrays a[0 ... n-1] and b[0 ... n-1] are equal
 * - return unknown if we can't tell
 */
value_t vtbl_eval_array_eq(value_table_t *table, value_t *a, value_t *b, uint32_t n) {
  uint32_t i;
  value_t v;

  for (i=0; i<n; i++) {
    assert(good_object(table, a[i]) && good_object(table, b[i]));

    if (a[i] != b[i]) {
      v = vtbl_eval_eq(table, a[i], b[i]);
      if (v == vtbl_mk_false(table) || v == vtbl_mk_unknown(table)) {
	return v;
      }
      assert(v == vtbl_mk_true(table));
    }
  }

  return vtbl_mk_true(table);
}


