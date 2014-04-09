/*
 * Concrete values = constants of different types.
 * This is used to build models: a model is a mapping from terms to concrete values.
 */

#include <inttypes.h>

#include "memalloc.h"
#include "hash_functions.h"
#include "int_array_sort.h"
#include "type_printer.h"
#include "concrete_values.h"




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
  table->canonical = allocate_bitvector(n);

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
  table->canonical = extend_bitvector(table->canonical, n);
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
 * Delete descriptors for objects i ... nobjects - 1
 */
static void vtbl_delete_descriptors(value_table_t *table, uint32_t i) {
  uint32_t n;

  n = table->nobjects;
  assert(i <= n);
  for (i=0; i<n; i++) {
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
  delete_bvconstant(&table->buffer);
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
 * There's a hobj for rationals and bitvectors.
 * Each hobj structure starts with a function descriptor m
 * with three fields:
 *   m.hash = compute hash code
 *   m.eq = check equality
 *   m.build = build a fresh value
 */
typedef struct {
  int_hobj_t m;
  value_table_t *table;
  rational_t v;
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
  q_hash_decompose(&o->v, &h_num, &h_den);
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
  return table->kind[i] == RATIONAL_VALUE && q_eq(&table->desc[i].rational, &o->v);
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
  q_set(&table->desc[i].rational, &o->v);
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
  q_init(&hobj.v);
  q_set(&hobj.v, v);

  return int_htbl_get_obj(&table->htbl, &hobj.m);
}

/*
 * Return a rational constant equal to i
 */
value_t vtbl_mk_int32(value_table_t *table, int32_t i) {
  rational_hobj_t hobj;

  hobj.m.hash = (hobj_hash_t) hash_rational_value;
  hobj.m.eq =  (hobj_eq_t) equal_rational_value;
  hobj.m.build = (hobj_build_t) build_rational_value;
  hobj.table = table;
  q_init(&hobj.v);
  q_set32(&hobj.v, i);

  return int_htbl_get_obj(&table->htbl, &hobj.m);
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
    // a and b are non canonical
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

  for (i=0; i<n; i++) {
    assert(good_object(table, a[i]) && good_object(table, b[i]));

    if (a[i] != b[i]) {
      if (object_is_canonical(table, a[i]) || object_is_canonical(table, b[i])) {
        return vtbl_mk_false(table);
      } else {
        return vtbl_mk_unknown(table);
      }
    }
  }

  return vtbl_mk_true(table);
}




/***************
 *  PRINTING   *
 **************/


/*
 * Printing for each object type
 */
static inline void vtbl_print_unknown(FILE *f) {
  fputs("???", f);
}

static inline void vtbl_print_bool(FILE *f, int32_t b) {
  if (b) {
    fputs("true", f);
  } else {
    fputs("false", f);
  }
}

static inline void vtbl_print_rational(FILE *f, rational_t *v) {
  q_print(f, v);
}

static inline void vtbl_print_bitvector(FILE *f, value_bv_t *b) {
  bvconst_print(f, b->data, b->nbits);
}



/*
 * Print object c on stream f
 */
void vtbl_print_object(FILE *f, value_table_t *table, value_t c) {
  assert(0 <= c && c < table->nobjects);
  switch (table->kind[c]) {
  case UNKNOWN_VALUE:
    vtbl_print_unknown(f);
    break;
  case BOOLEAN_VALUE:
    vtbl_print_bool(f, table->desc[c].integer);
    break;
  case RATIONAL_VALUE:
    vtbl_print_rational(f, &table->desc[c].rational);
    break;
  case BITVECTOR_VALUE:
    vtbl_print_bitvector(f, table->desc[c].ptr);
    break;
  default:
    assert(false);
  }
}




/*********************
 *  PRETTY PRINTING  *
 ********************/

/*
 * Printing for each object type
 */
static inline void vtbl_pp_bitvector(yices_pp_t *printer, value_bv_t *b) {
  pp_bv(printer, b->data, b->nbits);
}


/*
 * Print object c on stream f
 */
void vtbl_pp_object(yices_pp_t *printer, value_table_t *table, value_t c) {
  assert(0 <= c && c < table->nobjects);

  switch (table->kind[c]) {
  case UNKNOWN_VALUE:
    pp_string(printer, "???");
    break;
  case BOOLEAN_VALUE:
    pp_bool(printer, table->desc[c].integer);
    break;
  case RATIONAL_VALUE:
    pp_rational(printer, &table->desc[c].rational);
    break;
  case BITVECTOR_VALUE:
    vtbl_pp_bitvector(printer, table->desc[c].ptr);
    break;
  default:
    assert(false);
  }
}

