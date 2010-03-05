/*
 * Concrete values = constants of different types.
 * This is used to build models: a model is a mapping from terms to concrete values.
 */

#include <inttypes.h>

#include "memalloc.h"
#include "hash_functions.h"
#include "int_array_sort.h"
#include "concrete_values.h"




/************************
 *  AUXILIARY HASH MAP  *
 ***********************/

/*
 * Initialize table: empty table of default size
 */
static void init_map_htbl(map_htbl_t *htbl) {
  uint32_t i, n;
  map_pair_t *tmp;

  n = MAP_HTBL_DEFAULT_SIZE;
  assert(n < MAP_HTBL_MAX_SIZE);

  tmp = (map_pair_t *) safe_malloc(n * sizeof(map_pair_t));
  for (i=0; i<n; i++) {
    tmp[i].function = null_value; // mark as empty
  }

  htbl->data = tmp;
  htbl->size = n;
  htbl->nelems = 0;
  htbl->resize_threshold = (uint32_t) (MAP_HTBL_RESIZE_RATIO * n);
}



/*
 * Delete the table
 */
static void delete_map_htbl(map_htbl_t *htbl) {
  safe_free(htbl->data);
  htbl->data = NULL;
}


/*
 * Empty the table
 */
static void reset_map_htbl(map_htbl_t *htbl) {
  uint32_t i, n;

  n = htbl->size;
  for (i=0; i<n; i++) {
    htbl->data[i].function = null_value; // mark as empty
  }
  htbl->nelems = 0;
}




/*
 * Compute the hash code of (f a[0] ... a[n-1])
 * - f and a[0] ... a[n-1] must all be valid objects in vtbl
 */
static uint32_t hash_fun_app(value_t f, uint32_t n, value_t *a) {
  uint32_t h;

  h = jenkins_hash_intarray_var(n, a, 0x83421bca);
  return jenkins_hash_pair(f, 0, h);
}



/*
 * Compute the hash code of a pair (f, i)
 * - f must be a function object
 * - i must be a mapping object of same arity as f
 */
static uint32_t hash_map_pair(value_table_t *table, value_t f, value_t i) {
  value_map_t *map;

  assert(object_is_map(table, i) && object_is_function(table, f));
  map = (value_map_t *) table->desc[i].ptr;
  assert(map->arity == ((value_fun_t *) table->desc[f].ptr)->arity);
  return hash_fun_app(f, map->arity, map->arg);
}




/*
 * Check whether object i matches a[0] ... a[n-1]
 * - i must be a mapping object with n arguments
 * - i matches if a[0] = arg[0] ... a[n-1] = arg[n-1]
 */
static bool mapping_matches_array(value_table_t *table, value_t i, uint32_t n, value_t *a) {
  value_map_t *map;
  uint32_t j;

  assert(object_is_map(table, i));
  map = (value_map_t *) table->desc[i].ptr;
  assert(map->arity == n);

  for (j=0; j<n; j++) {
    if (a[j] != map->arg[j]) return false;
  }

  return true;
}



/*
 * Check whether object i and j match each other
 * - both must be mapping objects with the same number of arguments
 */
static bool mappings_match(value_table_t *table, value_t i, value_t j) {
  value_map_t *map1, *map2;
  uint32_t k, n;

  assert(object_is_map(table, i) && object_is_map(table, j));
  map1 = (value_map_t *) table->desc[i].ptr;
  map2 = (value_map_t *) table->desc[j].ptr;
  n = map1->arity;
  assert(map2->arity == n);

  for (k=0; k<n; k++) {
    if (map1->arg[k] != map2->arg[k]) return false;
  }

  return true;
}


/*
 * Search for a pair (f, k) in table such that k is of the form
 * (a[0] ... a[n-1] |-> v)
 * - vtbl = the value table where all objects are defined
 * - return v if such a pair is found, null_value otherwsie
 */
static value_t hash_eval_app(value_table_t *table, value_t f, uint32_t n, value_t *a) {
  map_pair_t *d;  
  uint32_t i, mask;
  value_t j;

  assert(table->mtbl.nelems < table->mtbl.size);

  mask = table->mtbl.size - 1;
  d = table->mtbl.data;
  i = hash_fun_app(f, n, a) & mask;
  for (;;) {
    if (d[i].function < 0) return null_value;
    if (d[i].function == f) {
      j = d[i].map;
      if (mapping_matches_array(table, j, n, a)) {
	return vtbl_map_result(table, j);
      }
    }
    i ++;
    i &= mask;
  }
}



/*
 * Copy pair p into a clean data array
 * - mask = size of data - 1 (data's size must be a power of 2)
 * - p must be a valid pair (i.e., p->function >= 0)
 * - there must be an empty slot in data
 */
static void map_htbl_clean_copy(value_table_t *table, map_pair_t *data, 
				map_pair_t *p, uint32_t mask) {
  uint32_t i;
  
  i = hash_map_pair(table, p->function, p->map) & mask;
  while (data[i].function >= 0) {
    i ++;
    i &= mask;
  }
  data[i] = *p;
}



/*
 * Make the hash table twice as large
 */
static void map_htbl_extend(value_table_t *table) {
  uint32_t n, n2;
  map_pair_t *tmp, *p;
  uint32_t i, mask;

  n = table->mtbl.size;
  n2 = n << 1;
  if (n2 >= MAP_HTBL_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (map_pair_t *) safe_malloc(n2 * sizeof(map_pair_t));
  for (i=0; i<n2; i++) {
    tmp[i].function = null_value;
  }

  mask = n2 - 1;
  p = table->mtbl.data;
  for (i=0; i<n; i++) {
    if (p->function >= 0) {
      map_htbl_clean_copy(table, tmp, p, mask);
    }
    p ++;
  }

  safe_free(table->mtbl.data);
  table->mtbl.data = tmp;
  table->mtbl.size = n2;
  table->mtbl.resize_threshold = (uint32_t) (MAP_HTBL_RESIZE_RATIO * n2);
}



/*
 * Add the pair (f, i) to the hash table
 * - there must not be a matching (f, j) in the table already
 */
static void add_hash_pair(value_table_t *table, value_t f, value_t i) {
  map_pair_t *d;
  uint32_t j, mask;

  assert(table->mtbl.nelems < table->mtbl.size);

  mask = table->mtbl.size - 1;
  d = table->mtbl.data;
  j = hash_map_pair(table, f, i) & mask;
  while (d[j].function >= 0) {
    assert(d[j].function != f || !mappings_match(table, i, d[j].map));
    j ++;
    j &= mask;
  }

  assert(d[j].function = null_value);
  d[j].function = f;
  d[j].map = i;

  table->mtbl.nelems ++;
  if (table->mtbl.nelems > table->mtbl.resize_threshold) {
    map_htbl_extend(table);
  }

}




/****************************************
 *  HASH SETS FOR UPDATE NORMALIZATION  *
 ***************************************/

/*
 * Initialize hset: use the default size
 */
static void init_map_hset(map_hset_t *hset) {
  uint32_t i, n;
  value_t *tmp;

  n = MAP_HSET_DEFAULT_SIZE;
  assert(n < MAP_HSET_MAX_SIZE);

  tmp = (value_t *) safe_malloc(n * sizeof(value_t));
  for (i=0; i<n; i++) {
    tmp[i] = null_value;
  }

  hset->data = tmp;
  hset->size = n;
  hset->nelems = 0;
  hset->resize_threshold = (uint32_t) (MAP_HSET_RESIZE_RATIO * n);
}


/*
 * Delete hset
 */
static void delete_map_hset(map_hset_t *hset) {
  safe_free(hset->data);
  hset->data = NULL;
}


/*
 * Empty hset
 */
static void reset_map_hset(map_hset_t *hset) {
  uint32_t i, n;

  n = hset->size;
  if (n >= MAP_HSET_REDUCE_THRESHOLD) {
    // reduce data to an array of default size
    safe_free(hset->data);

    n = MAP_HSET_DEFAULT_SIZE;
    assert(n < MAP_HSET_MAX_SIZE && n < MAP_HSET_REDUCE_THRESHOLD);
    hset->data = (value_t *) safe_malloc(n * sizeof(value_t));
    hset->size = n;
    hset->resize_threshold = (uint32_t) (MAP_HSET_RESIZE_RATIO * n);
  }

  // empty data
  for (i=0; i<n; i++) {
    hset->data[i] = null_value;
  }
  hset->nelems = 0;
}



/*
 * Hash code for mapping object i
 */
static uint32_t hash_map_object(value_table_t *table, value_t i) {
  value_map_t *map;

  assert(object_is_map(table, i));
  map = (value_map_t *) table->desc[i].ptr;
  return jenkins_hash_intarray_var(map->arity, map->arg, 0x543f1a83);
}



/*
 * Copy v into clean array d
 * - mask = size of d - 1, where size of d is a power of 2
 */
static void map_hset_clean_copy(value_table_t *table, value_t *d, value_t v, uint32_t mask) {
  uint32_t i;

  i = hash_map_object(table, v) & mask;
  while (d[i] >= 0) {
    i++;
    i &= mask;
  }
  d[i] = v;
}


/*
 * Make the hset twice as large. Keep its content.
 */
static void map_hset_extend(value_table_t *table, map_hset_t *hset) {
  uint32_t n, n2;
  value_t *d, *p;
  uint32_t i, mask;

  n = hset->size;
  n2 = n<<1;
  if (n2 >= MAP_HSET_MAX_SIZE) {
    out_of_memory();
  }

  d = (value_t *) safe_malloc(n2 * sizeof(value_t));
  for (i=0; i<n2; i++) {
    d[i] = null_value;
  }

  mask = n2 - 1;
  p = hset->data;
  for (i=0; i<n; i++) {
    if (p[i] >= 0) {
      map_hset_clean_copy(table, d, p[i], mask);
    }
  }

  safe_free(p);
  hset->data = d;
  hset->size = n2;
  hset->resize_threshold = (uint32_t) (MAP_HSET_RESIZE_RATIO * n2);
}



/*
 * Add mapping object i to hset:
 * - no change if i matches an existing element in hset
 */
static void hset_add_map(value_table_t *table, map_hset_t *hset, value_t i) {
  value_t *d;
  value_t k;
  uint32_t j, mask;

  assert(hset->nelems < hset->size);

  mask = hset->size - 1;
  d = hset->data;
  j = hash_map_object(table, i) & mask;
  for (;;) {
    k = d[j];
    if (k < 0) break;   // add i
    if (mappings_match(table, i, k)) return; // k has precedence 
    j ++;
    j &= mask;
  }

  d[j] = i;
  hset->nelems ++;
  if (hset->nelems > hset->resize_threshold) {
    map_hset_extend(table, hset);
  }
}


/*
 * Normalize: collect all elements of hset into hset->data[0 ... n-1]
 * where n = hset->nelems and sort the elements.
 *
 * No addition is possible after normalization.
 */
static void hset_normalize(map_hset_t *hset) {
  value_t *d;
  uint32_t i, j, n;

  d = hset->data;
  n = hset->size;
  j = 0;
  for (i=0; i<n; i++) {
    if (d[i] >= 0) {
      d[j] = d[i];
      j ++;
    }
  }
  assert(j == hset->nelems);
  int_array_sort(d, j);
}








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
  init_map_htbl(&table->mtbl);

  table->hset1 = NULL;
  table->hset2 = NULL;

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
 * Return hset1 or hset2 (allocate and initialize it if needed)
 */
static map_hset_t *get_hset1(value_table_t *table) {
  map_hset_t *set;

  set = table->hset1;
  if (set == NULL) {
    set = (map_hset_t *) safe_malloc(sizeof(map_hset_t));
    init_map_hset(set);
    table->hset1 = set;
  }
  return set;
}

static map_hset_t *get_hset2(value_table_t *table) {
  map_hset_t *set;

  set = table->hset1;
  if (set == NULL) {
    set = (map_hset_t *) safe_malloc(sizeof(map_hset_t));
    init_map_hset(set);
    table->hset1 = set;
  }
  return set;
}



/*
 * Delete hset1 and hset2 if they exist
 */
static void delete_hsets(value_table_t *table) {
  if (table->hset1 != NULL) {
    delete_map_hset(table->hset1);
    safe_free(table->hset1);
    table->hset1 = NULL;
  }

  if (table->hset2 != NULL) {
    delete_map_hset(table->hset2);
    safe_free(table->hset2);
    table->hset2 = NULL;
  }
}


/*
 * Reset hset1 and hset2 if they exist
 */
static void reset_hsets(value_table_t *table) {
  if (table->hset1 != NULL) {
    reset_map_hset(table->hset1);
  }
  if (table->hset2 != NULL) {
    reset_map_hset(table->hset2);
  }
}




/*
 * Delete object descriptors
 */
static inline void delete_value_unint(value_unint_t *d) {
  safe_free(d->name);
  safe_free(d);
}

static inline void delete_value_fun(value_fun_t *d) {
  safe_free(d->name);
  safe_free(d);
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
    case UNINTERPRETED_VALUE:
      delete_value_unint(table->desc[i].ptr);
      break;
    case FUNCTION_VALUE:
      delete_value_fun(table->desc[i].ptr);
      break;
    case BITVECTOR_VALUE:
    case TUPLE_VALUE:
    case MAP_VALUE:
    case UPDATE_VALUE:
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
  reset_map_htbl(&table->mtbl);
  reset_hsets(table);

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
  delete_map_htbl(&table->mtbl);
  delete_hsets(table);
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
 * Uninterpreted constant of type tau
 * - tau must be a scalar or uninterpreted type
 * - if name is non-NULL then a copy is made
 * This function always create a new object and the index is set to -1.
 */
value_t vtbl_mk_unint(value_table_t *table, type_t tau, char *name) {
  value_unint_t *d;
  value_t i;

  assert(type_kind(table->type_table, tau) == SCALAR_TYPE || 
	 type_kind(table->type_table, tau) == UNINTERPRETED_TYPE);

  d = (value_unint_t *) safe_malloc(sizeof(value_unint_t));
  d->type = tau;
  d->index = -1;
  d->name = NULL;
  if (name != NULL) {
    d->name = (char *) safe_malloc(strlen(name) + 1);
    strcpy(d->name, name);
  }

  i = allocate_object(table);
  table->kind[i] = UNINTERPRETED_VALUE;
  table->desc[i].ptr = d;
  set_bit(table->canonical, i);

  return i;
}






/********************************************
 *  NORMALIZATION OF FUNCTIONS AND UPDATES  *
 *******************************************/

/*
 * Normalize an array of mapping objects a[0 ... n-1]
 * - sort a and remove duplicates
 * - return the number of elements left in a
 */
static uint32_t normalize_map_array(uint32_t n, value_t *a) {
  uint32_t i, j;
  value_t v, w;
  
  if (n > 1) {
    int_array_sort(a, n);
    j = 1;
    v = a[0];
    for (i=1; i<n; i++) {
      w = a[i];
      if (v != w) {
	a[j] = w;
	j ++;
	v = w;
      }
    }
    n = j;
  }

  return n;
}



/*
 * Remove all elements in array a[0 ... n-1] that give the same 
 * value as def.
 * - return the number of elements left in a
 */
static uint32_t remove_redundant_mappings(value_table_t *table, uint32_t n, value_t *a, value_t def) {
  uint32_t i, j;
  value_t v;

  j = 0;
  for (i=0; i<n; i++) {
    v = a[i];
    if (vtbl_map_result(table, v) != def) {
      a[j] = v;
      j++;
    }
  }

  return j;
}



/*
 * Compute the set of mapping objects for i
 * - i must be an update value or a function
 * - hset = where the set is stored
 * - def = address where default value will be copied
 * - tau = address where the function type will be copied
 *
 * The mapping objects are added to hset then hset is normalized.
 * Whatever is in hset when the function is called is kept.
 * The default value and type of the function are copied into
 * *def and *tau
 */
static void normalize_update(value_table_t *table, value_t i, map_hset_t *hset, 
			     value_t *def, type_t *tau) { 
  value_update_t *upd;
  value_fun_t *fun;
  uint32_t j, n;

  while (object_is_update(table, i)) {
    upd = (value_update_t *) table->desc[i].ptr;
    hset_add_map(table, hset, upd->map);
    i = upd->fun;
  }

  assert(object_is_function(table, i));
  fun = (value_fun_t *) table->desc[i].ptr;
  *def = fun->def;
  *tau = fun->type;
  n = fun->map_size;
  for (j=0; j<n; j++) {
    hset_add_map(table, hset, fun->map[j]);
  }

  hset_normalize(hset);

  // the mappings are in hset->data[0.. nelems-1]
  if (! object_is_unknown(table, *def)) {
    n = remove_redundant_mappings(table, hset->nelems, hset->data, *def);
    hset->nelems = n;
  }
}





/***************
 *  UTILITIES  *
 **************/

/*
 * Check whether a and b are equal arrays
 * - both must have size n
 */
static bool equal_arrays(value_t *a, value_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}


/* 
 * Check whether all elements in a are canonical
 */
static bool canonical_array(value_table_t *table, value_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (! object_is_canonical(table, a[i])) {
      return false;
    }
  }

  return true;
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
 *
 * For map objects, hash-consing relies only on the function and arguments:
 * - all map objects with the same function must have the same number of arguments.
 * - two maps objects with the same function and arguments must also have the 
 *   same result.
 */
typedef struct {
  int_hobj_t m;
  value_table_t *table;
  rational_t v;
} rational_hobj_t;

typedef struct {
  int_hobj_t m;
  value_table_t *table;
  type_t tau;
  int32_t id;
} const_hobj_t;

typedef struct {
  int_hobj_t m;
  value_table_t *table;
  uint32_t nbits;
  uint32_t *data;  // must be normalized modulo (2^nbits)
} bv_hobj_t;

typedef struct {
  int_hobj_t m;
  value_table_t *table;
  uint32_t nelems;
  value_t *elem;
} tuple_hobj_t;

typedef struct {
  int_hobj_t m;
  value_table_t *table;
  uint32_t arity;
  value_t *arg;
  value_t val;
} map_hobj_t;



/*
 * Function representation:
 * - a default value (can be unknown)
 * - an array map[0... n-1] of mapping objects sorted
 */
typedef struct {
  int_hobj_t m;
  value_table_t *table;
  type_t type;
  uint32_t arity;
  value_t def;
  uint32_t map_size;
  value_t *map;
  bool ambiguous;
} fun_hobj_t;


/*
 * Function update: for hash-consing, the update
 * is converted into a function representation as above
 * - default value + map array
 */
typedef struct {
  int_hobj_t m;
  value_table_t *table;
  type_t type;
  uint32_t arity;
  value_t fun;
  value_t updt;
  
  value_t def;
  uint32_t map_size;
  value_t *map;
  bool ambiguous;
} update_hobj_t;


/*
 * Hash functions
 */
static uint32_t hash_rational_value(rational_hobj_t *o) {
  uint32_t h_num, h_den;
  q_hash_decompose(&o->v, &h_num, &h_den);
  return jenkins_hash_mix2(h_num, h_den);
}

static uint32_t hash_const_value(const_hobj_t *o) {
  return jenkins_hash_pair(o->tau, o->id, 0x417a6eca);
}

static uint32_t hash_bv_value(bv_hobj_t *o) {
  return bvconst_hash(o->data, o->nbits);
}

static uint32_t hash_tuple_value(tuple_hobj_t *o) {
  return jenkins_hash_intarray_var(o->nelems, o->elem, 0x21398aba);
}

static uint32_t hash_map_value(map_hobj_t *o) {
  uint32_t h;

  h = jenkins_hash_intarray_var(o->arity, o->arg, 0xabde6320);
  return jenkins_hash_pair(o->val, 0, h);
}

static uint32_t hash_fun_value(fun_hobj_t *o) {
  uint32_t h;

  h = jenkins_hash_intarray_var(o->map_size, o->map, 0x9765aef5);
  return jenkins_hash_pair(o->def, 0, h);
}

static uint32_t hash_update_value(update_hobj_t *o) {
  uint32_t h;

  h = jenkins_hash_intarray_var(o->map_size, o->map, 0x9765aef5);
  return jenkins_hash_pair(o->def, 0, h);
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

static bool equal_const_value(const_hobj_t *o, value_t i) {
  value_table_t *table;
  value_unint_t *d;

  table = o->table;
  if (table->kind[i] != UNINTERPRETED_VALUE) {
    return false;
  }
  d = table->desc[i].ptr;
  return d->type == o->tau && d->index == o->id;
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


static bool equal_tuple_value(tuple_hobj_t *o, value_t i) {
  value_table_t *table;
  value_tuple_t *d;

  table = o->table;
  if (table->kind[i] != TUPLE_VALUE) {
    return false;
  }
  d = table->desc[i].ptr;
  return d->nelems == o->nelems && equal_arrays(o->elem, d->elem, d->nelems);
}

static bool equal_map_value(map_hobj_t *o, value_t i) {
  value_table_t *table;
  value_map_t *d;

  table = o->table;
  if (table->kind[i] != MAP_VALUE) {
    return false;
  }
  d = table->desc[i].ptr;
  return d->val == o->val && d->arity == o->arity && equal_arrays(o->arg, d->arg, d->arity);
}



static bool equal_fun_value(fun_hobj_t *o, value_t i) {
  value_table_t *table;
  value_fun_t *f;
  map_hset_t *hset;
  type_t tau;
  value_t def;

  table = o->table;
  switch (table->kind[i]) {
  case FUNCTION_VALUE:
    f = (value_fun_t *) table->desc[i].ptr;
    return f->type == o->type && f->def == o->def 
      && f->map_size == o->map_size 
      && equal_arrays(f->map, o->map, o->map_size);

  case UPDATE_VALUE:
    hset = get_hset2(table);
    reset_map_hset(hset);
    normalize_update(table, i, hset, &def, &tau);
    return tau == o->type &&  def == o->def 
      && o->map_size == hset->nelems 
      && equal_arrays(hset->data, o->map, o->map_size);

  default:
    return false;
  }
}


static bool equal_update_value(update_hobj_t *o, value_t i) {
  value_table_t *table;
  value_fun_t *f;
  map_hset_t *hset;
  type_t tau;
  value_t def;

  table = o->table;
  switch (table->kind[i]) {
  case FUNCTION_VALUE:
    f = (value_fun_t *) table->desc[i].ptr;
    return f->type == o->type && f->def == o->def 
      && f->map_size == o->map_size 
      && equal_arrays(f->map, o->map, o->map_size);

  case UPDATE_VALUE:
    hset = get_hset2(table);
    reset_map_hset(hset);
    normalize_update(table, i, hset, &def, &tau);
    return tau == o->type &&  def == o->def 
      && o->map_size == hset->nelems 
      && equal_arrays(hset->data, o->map, o->map_size);

  default:
    return false;
  }
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

static value_t build_const_value(const_hobj_t *o) {
  value_table_t *table;
  value_unint_t *d;
  value_t i;

  d = (value_unint_t *) safe_malloc(sizeof(value_unint_t));
  d->type = o->tau;
  d->index = o->id;
  d->name = NULL;


  table = o->table;
  i = allocate_object(table);
  table->kind[i] = UNINTERPRETED_VALUE;
  table->desc[i].ptr = d;
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


static value_t build_tuple_value(tuple_hobj_t *o) {
  value_table_t *table;
  value_tuple_t *d;
  uint32_t j, n;
  value_t i;


  n = o->nelems;
  if (n >= VTBL_MAX_TUPLE_SIZE) {
    out_of_memory();
  }
  d = (value_tuple_t *) safe_malloc(sizeof(value_tuple_t) + n * sizeof(value_t));
  d->nelems = n;
  for (j=0; j<n; j++) {
    d->elem[j] = o->elem[j];
    
  }
  
  table = o->table;
  i = allocate_object(table);
  table->kind[i] = TUPLE_VALUE;
  table->desc[i].ptr = d;

  if (canonical_array(table, d->elem, n)) {
    set_bit(table->canonical, i);
  } else {
    clr_bit(table->canonical, i);
  }

  return i;
}


static value_t build_map_value(map_hobj_t *o) {
  value_table_t *table;
  value_map_t *d;
  uint32_t j, n;
  value_t i;

  n = o->arity;
  if (n >= VTBL_MAX_MAP_ARITY) {
    out_of_memory();
  }
  d = (value_map_t *) safe_malloc(sizeof(value_map_t) + n * sizeof(value_t));
  d->arity = n;
  d->val = o->val;
  for (j=0; j<n; j++) {
    d->arg[j] = o->arg[j];
  }

  table = o->table;
  i = allocate_object(table);
  table->kind[i] = MAP_VALUE;
  table->desc[i].ptr = d;

  if (canonical_array(table, d->arg, n) && object_is_canonical(table, d->val)) {
    set_bit(table->canonical, i);
  } else {
    clr_bit(table->canonical, i);
  }

  return i;
}


static value_t build_fun_value(fun_hobj_t *o) {
  value_table_t *table;
  value_fun_t *fun;
  value_t f, i;
  uint32_t j, n;

  table = o->table;

  n = o->map_size;
  if (n >= VTBL_MAX_MAP_SIZE) {
    out_of_memory();
  }
  fun = (value_fun_t *) safe_malloc(sizeof(value_fun_t) + n * sizeof(value_t));
  fun->name = NULL;
  fun->type = o->type;
  fun->arity = o->arity;
  fun->map_size = n;
  fun->def = o->def;

  f = allocate_object(table);
  table->kind[f] = FUNCTION_VALUE;
  table->desc[f].ptr = fun;

  for (j=0; j<n; j++) {
    i = o->map[j];
    fun->map[j] = i;
    add_hash_pair(table, f, i);
  }

  // set the canonical flag
  if (!o->ambiguous && object_is_canonical(table, fun->def) && 
      canonical_array(table, fun->map, n)) {
    set_bit(table->canonical, f);
  } else {
    clr_bit(table->canonical, f);
  }

  return f;
}


static value_t build_update_value(update_hobj_t *o) {
  value_table_t *table;
  value_update_t *d;
  value_t i;

  d = (value_update_t *) safe_malloc(sizeof(value_update_t));
  d->arity = o->arity;
  d->fun = o->fun;
  d->map = o->updt;

  table = o->table;
  i = allocate_object(table);
  table->kind[i] = UPDATE_VALUE;
  table->desc[i].ptr = d;

  // set the canonical flag
  if (!o->ambiguous && object_is_canonical(table, o->def) && 
      canonical_array(table, o->map, o->map_size)) {
    set_bit(table->canonical, i);
  } else {
    clr_bit(table->canonical, i);
  }

  return i;
}




/*
 * Hash-consing objects for int_htbl
 */
static rational_hobj_t rational_hobj = {
  { (hobj_hash_t) hash_rational_value, (hobj_eq_t) equal_rational_value, (hobj_build_t) build_rational_value },
  NULL,
  { 0, 1}, // represents rational zero
};

static const_hobj_t const_hobj = {
  { (hobj_hash_t) hash_const_value, (hobj_eq_t) equal_const_value, (hobj_build_t) build_const_value },
  NULL,
  0,
  0,
};

static bv_hobj_t bv_hobj = {
  { (hobj_hash_t) hash_bv_value, (hobj_eq_t) equal_bv_value, (hobj_build_t) build_bv_value },
  NULL,
  0, NULL,
};

static tuple_hobj_t tuple_hobj = {
  { (hobj_hash_t) hash_tuple_value, (hobj_eq_t) equal_tuple_value, (hobj_build_t) build_tuple_value },
  NULL,
  0, NULL,
};

static map_hobj_t map_hobj = {
  { (hobj_hash_t) hash_map_value, (hobj_eq_t) equal_map_value, (hobj_build_t) build_map_value },
  NULL,
  0, NULL, 0,
};


static fun_hobj_t fun_hobj = {
  { (hobj_hash_t) hash_fun_value, (hobj_eq_t) equal_fun_value, (hobj_build_t) build_fun_value },
  NULL,
  0, 0, 0, 0, NULL,
};


static update_hobj_t update_hobj = {
  { (hobj_hash_t) hash_update_value, (hobj_eq_t) equal_update_value, (hobj_build_t) build_update_value },
  NULL,
  0, 0, 0, 0, 0, 0, NULL,
};



/*
 * Return a rational constant = v
 */
value_t vtbl_mk_rational(value_table_t *table, rational_t *v) {
  rational_hobj.table = table;
  q_set(&rational_hobj.v, v);

  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &rational_hobj);
}

/*
 * Return a rational constant equal to i
 */
value_t vtbl_mk_int32(value_table_t *table, int32_t i) {
  rational_hobj.table = table;
  q_set32(&rational_hobj.v, i);

  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &rational_hobj);
}



/*
 * Bit vector constant: defined by array a:
 * - a[i] = 0 means bit[i] = 0
 * - a[i] != 0 means bit[i] = 1
 */
value_t vtbl_mk_bv(value_table_t *table, uint32_t n, int32_t *a) {
  bvconstant_t *b;

  // copy the constant in table's buffer
  b = &table->buffer;
  bvconstant_set_bitsize(b, n);
  bvconst_set_array(b->data, a, n);
  bvconst_normalize(b->data, n);

  // hash-consing
  bv_hobj.table = table;
  bv_hobj.nbits = n;
  bv_hobj.data = b->data;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &bv_hobj);
}



/*
 * Bit vector constant defined by an array of words
 * - n = number of bits
 * - a = array of w words (w = ceil(n/32)
 */
value_t vtbl_mk_bv_from_bv(value_table_t *table, uint32_t n, uint32_t *a) {
  bvconst_normalize(a, n);  

  bv_hobj.table = table;
  bv_hobj.nbits = n;
  bv_hobj.data = a;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t*) &bv_hobj);  
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
 * Tuple (e[0] ... e[n-1])
 */
value_t vtbl_mk_tuple(value_table_t *table, uint32_t n, value_t *e) {
  tuple_hobj.table = table;
  tuple_hobj.nelems = n;
  tuple_hobj.elem = e;

  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &tuple_hobj);
}


/*
 * Constant of type tau and index id
 * - name = optional name
 */
value_t vtbl_mk_const(value_table_t *table, type_t tau, int32_t id, char *name) {
  value_unint_t *d;
  value_t v;

  assert(type_kind(table->type_table, tau) == SCALAR_TYPE || 
	 type_kind(table->type_table, tau) == UNINTERPRETED_TYPE);
  assert(0 <= id);

  const_hobj.table = table;
  const_hobj.tau = tau;
  const_hobj.id = id;
  v = int_htbl_get_obj(&table->htbl, (int_hobj_t *) &const_hobj);

  // set the name if needed
  assert(table->kind[v] == UNINTERPRETED_VALUE);
  d = table->desc[v].ptr;
  if (name != NULL && d->name == NULL) {
    d->name = (char *) safe_malloc(strlen(name) + 1);
    strcpy(d->name, name);
  }

  return v;
}




/*
 * Mapping object (a[0] ... a[n-1]  |-> v)
 * - return a mapping object
 */
value_t vtbl_mk_map(value_table_t *table, uint32_t n, value_t *a, value_t v) {
  map_hobj.table = table;
  map_hobj.arity = n;
  map_hobj.arg = a;
  map_hobj.val = v;

  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &map_hobj);
}




/*
 * Function defined by the array a[0...n] and default value def
 * - tau = its type
 * - name = optional name (or NULL). If name is no NULL, a copy is made.
 * - a = array of n mapping objects. 
 *   The array must not contain conflicting mappings and all elements in a
 *   must have the right arity (same as defined by type tau). It's allowed
 *   to have duplicate elements in a.
 * - def = default value (must be unknown if no default is given)
 *
 * NOTE: a is modified by the function.
 */
value_t vtbl_mk_function(value_table_t *table, type_t tau, uint32_t n, value_t *a, value_t def, char *name) {
  assert(good_object(table, def));

  // normalize a
  n = normalize_map_array(n, a);
  if (! object_is_unknown(table, def)) {
    n = remove_redundant_mappings(table, n, a, def);
  }


  fun_hobj.table = table;
  fun_hobj.type = tau;
  fun_hobj.arity = function_type_ndomains(table->type_table, tau);
  fun_hobj.def = def;
  fun_hobj.map_size = n;
  fun_hobj.map = a;

  /*
   * Check whether the pair (map + default) is a canonical representation
   * for this function. The representation is ambiguous if the same function
   * can be represented via another pair (map1 + default1).
   *
   * This happens if the function has a finite domain and the 
   * default value is something other than unknown. 
   */
  fun_hobj.ambiguous = type_has_finite_domain(table->type_table, tau) && 
    !object_is_unknown(table, def);

  return int_htbl_get_obj(&table->htbl, (int_hobj_t*) &fun_hobj);
}



/*
 * Create (update f (a[0] ... a[n-1]) v)
 */
value_t vtbl_mk_update(value_table_t *table, value_t f, uint32_t n, value_t *a, value_t v) {
  map_hset_t *hset;
  value_t u;
  value_t def;
  type_t tau;

  // build the mapping [a[0] ... a[n-1] --> v]
  u = vtbl_mk_map(table, n, a, v);

  // normalize: add mapping u + normalization of f
  hset = get_hset1(table);
  reset_map_hset(hset);
  hset_add_map(table, hset, u);
  normalize_update(table, f, hset, &def, &tau);


  // hash consing 
  update_hobj.table = table;
  update_hobj.type = tau;
  update_hobj.arity = function_type_ndomains(table->type_table, tau);
  update_hobj.fun = f;
  update_hobj.updt = u;
  update_hobj.def = def;
  update_hobj.map_size = hset->nelems;
  update_hobj.map = hset->data;
  update_hobj.ambiguous = type_has_finite_domain(table->type_table, tau) &&
    !object_is_unknown(table, def);

  return int_htbl_get_obj(&table->htbl, (int_hobj_t*) &update_hobj);
}









/*****************************
 *  FUNCTION/CONSTANT NAMES  *
 ****************************/

/*
 * Set the name of a function f (make a copy and overwrite the current name)
 */
void vtbl_set_function_name(value_table_t *table, value_t f, char *name) {
  value_fun_t *fun;

  assert(table->kind[f] == FUNCTION_VALUE);
  fun = table->desc[f].ptr;
  if (fun->name != NULL) {
    safe_free(fun->name);
    fun->name = NULL;
  }
  if (name != NULL) {
    fun->name = (char *) safe_malloc(strlen(name) + 1);
    strcpy(fun->name, name);
  }
}


/*
 * Set the name of an uninterpreted constant c
 */
void vtbl_set_constant_name(value_table_t *table, value_t c, char *name) {
  value_unint_t *d;

  assert(table->kind[c] == UNINTERPRETED_VALUE);
  d = table->desc[c].ptr;
  if (d->name != NULL) {
    safe_free(d->name);
    d->name = NULL;
  }
  if (name != NULL) {
    d->name = (char *) safe_malloc(strlen(name) + 1);
    strcpy(d->name, name);
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
 * Check whether every element in the domain and range of f
 * is canonical. 
 * - f must be a function
 */
static bool semi_canonical(value_table_t *table, value_t f) {
  value_fun_t *fun;

  fun = vtbl_function(table, f);
  return object_is_canonical(table, fun->def) && canonical_array(table, fun->map, fun->map_size);
}


/*
 * Evaluate (eq a b)
 *
 * TODO: improve this. We could do much more when checking equality
 * between two functions.
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
    if (object_is_function(table, a) && object_is_function(table, b) && 
	semi_canonical(table, a) && semi_canonical(table, b) && 
	vtbl_function(table, a)->def == vtbl_function(table, b)->def) {
      // since the two maps have the same default value, there's no ambiguity
      v = vtbl_mk_false(table);
    } else {
      v = vtbl_mk_unknown(table);
    }
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



/*
 * Evaluate (f a[0] ... a[n-1])
 * - f must be a function or update object of arity n
 * - a[0] ... a[n-1] must be non-null values
 * Return unknown if the map is not defined for a[0 ... n-1]
 */
value_t vtbl_eval_application(value_table_t *table, value_t f, uint32_t n, value_t *a) {
  value_update_t *u;
  value_t j;

  // unroll all updates
  while (object_is_update(table, f)) {
    u = table->desc[f].ptr;
    assert(u->arity == n);
    j = u->map;
    if (mapping_matches_array(table, j, n, a)) {
      return vtbl_map_result(table, j);
    }
    f = u->fun;
  }

  assert(object_is_function(table, f) && vtbl_function(table, f)->arity == n);

  // search for (f a[0] ... a[n-1]) in the mtbl
  j = hash_eval_app(table, f, n, a);
  if (j == null_value) {
    if (canonical_array(table, a, n)) {
      // use the default value for f
      j = vtbl_function(table, f)->def;
    } else {
      // can't tell for sure so we return unknown
      j = vtbl_mk_unknown(table);
    }
  }

  return j;
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
 * For uninterpreted constant and function.
 * We print a default name if there's no name given.
 */
static void vtbl_print_unint_name(FILE *f, value_t c, value_unint_t *v) {
  if (v->name == NULL) {
    fprintf(f, "const!%"PRId32, c);
  } else {
    fputs(v->name, f);
  }
}

static void vtbl_print_fun_name(FILE *f, value_t c, value_fun_t *fun) {
  if (fun->name == NULL) {
    fprintf(f, "fun!%"PRId32, c);
  } else {
    fputs(fun->name, f);
  }
}



/*
 * For tuples, maps, and updates: recursively print elements
 */
static void vtbl_print_tuple(FILE *f, value_table_t *table, value_tuple_t *t) {
  uint32_t i, n;

  n = t->nelems;
  fputs("(mk-tuple", f);
  for (i=0; i<n; i++) {
    fputc(' ', f);
    vtbl_print_object(f, table, t->elem[i]);
  }
  fputc(')', f);
}


static void vtbl_print_map(FILE *f, value_table_t *table, value_map_t *m) {
  uint32_t i, n;

  fputc('[', f);
  n = m->arity;
  for (i=0; i<n; i++) {
    vtbl_print_object(f, table, m->arg[i]);
    fputc(' ', f);
  }
  fputs("|-> ", f);
  vtbl_print_object(f, table, m->val);
  fputc(']', f);
}


static void vtbl_print_update(FILE *f, value_table_t *table, value_update_t *u) {
  value_map_t *m;
  uint32_t i, n;

  n = u->arity;
  assert(n > 0);

  m = vtbl_map(table, u->map);
  assert(m->arity == n);

  fputs("(update ", f);
  vtbl_print_object(f, table, u->fun);
  fputs(" (", f);
  vtbl_print_object(f, table, m->arg[0]);
  for (i=1; i<n; i++) {
    fputc(' ', f);
    vtbl_print_object(f, table, m->arg[i]);
  }
  fputs(") ", f);
  vtbl_print_object(f, table, m->val);
  fputc(')', f);
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
  case TUPLE_VALUE:
    vtbl_print_tuple(f, table, table->desc[c].ptr);
    break;
  case UNINTERPRETED_VALUE:
    vtbl_print_unint_name(f, c, table->desc[c].ptr);
    break;
  case FUNCTION_VALUE:
    vtbl_print_fun_name(f, c, table->desc[c].ptr);
    break;
  case MAP_VALUE:
    vtbl_print_map(f, table, table->desc[c].ptr);
    break;
  case UPDATE_VALUE:
    vtbl_print_update(f, table, table->desc[c].ptr);
    break;
  default:
    assert(false);
  }
}


#if 0
/*
 * Print a line that describes the default value of a function c
 */
static void vtbl_print_default(FILE *f, value_table_t *table, value_t c, value_fun_t *fun) {
  uint32_t i, n;

  fputs("(= (", f);
  vtbl_print_fun_name(f, c, fun);
  n = fun->arity;
  for (i=0; i<n; i++) {
    fprintf(f, " x!%"PRId32, i);
  }
  fputs(") ", f);
  vtbl_print_object(f, table, fun->def);
  fputs(")", f);
}

#endif

/*
 * Print the function c
 * - if show_default is true, also print the default falue
 */
void vtbl_print_function(FILE *f, value_table_t *table, value_t c, bool show_default) {
  value_fun_t *fun;
  value_map_t *mp;
  uint32_t i, n;
  uint32_t j, m;

  assert(0 <= c && c < table->nobjects && table->kind[c] == FUNCTION_VALUE);
  fun = table->desc[c].ptr;
  // header: may be removed later
  fputs("--- ", f);
  vtbl_print_fun_name(f, c, fun);
  fputs(" ---\n", f);

  m = fun->arity;
  n = fun->map_size;
  for (i=0; i<n; i++) {
    fputs("(= (", f);
    vtbl_print_fun_name(f, c, fun);

    mp = vtbl_map(table, fun->map[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      fputc(' ', f);
      vtbl_print_object(f, table, mp->arg[j]);
    }
    fputs(") ", f);
    vtbl_print_object(f, table, mp->val);    
    fputs(")\n", f);
  }

  if (show_default) {
    if (is_unknown(table, fun->def)) {
      fputs("no default\n", f);
    } else {
      fputs("default: ", f);
      vtbl_print_object(f, table, fun->def);
      fputc('\n', f);
    }
  }
}


/*
 * Expand update c and print it as a function
 * - name = function name to use
 * - if show_default is true, also print the default value
 */
void vtbl_normalize_and_print_update(FILE *f, value_table_t *table, char *name, value_t c, bool show_default) {
  map_hset_t *hset;
  value_map_t *mp;
  value_t def;
  type_t tau;
  uint32_t i, j, n, m;

  assert(0 <= c && c < table->nobjects && table->kind[c] == UPDATE_VALUE);
  
  // build the mapping for c in hset1
  hset = get_hset1(table);
  reset_map_hset(hset);
  normalize_update(table, c, hset, &def, &tau);

  /*
   * hset->data contains an array of mapping objects
   * hset->nelems = number of elements in hset->data
   */
  // print function header
  fprintf(f, "--- %s ---\n", name);

  m = vtbl_update(table, c)->arity;
  n = hset->nelems;
  for (i=0; i<n; i++) {
    fprintf(f, "(= (%s", name);

    mp = vtbl_map(table, hset->data[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      fputc(' ', f);
      vtbl_print_object(f, table, mp->arg[j]);
    }
    fputs(") ", f);
    vtbl_print_object(f, table, mp->val);
    fputs(")\n", f);
  }

  if (show_default) {
    if (is_unknown(table, def)) {
      fputs("no default\n", f);
    } else {
      fputs("default: ", f);
      vtbl_print_object(f, table, def);
      fputc('\n', f);
    }
  }
}



/*
 * Print the maps defining the anonymous functions
 * - i.e., all functions whose name is NULL
 * - if show_default is true, print the default value for each map
 */
void vtbl_print_anonymous_functions(FILE *f, value_table_t *table, bool show_default) {
  value_fun_t *fun;
  uint32_t i, n;

  n = table->nobjects;
  for (i=0; i<n; i++) {
    if (object_is_function(table, i)) {
      fun = table->desc[i].ptr;
      if (fun->name == NULL) {
	vtbl_print_function(f, table, i, show_default);
      }
    }	
  }
}
