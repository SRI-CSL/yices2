/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * DESCRIPTORS OF CONCRETE VALUES
 */

#include <assert.h>

#include "api/yval.h"
#include "utils/memalloc.h"


/*
 * Initialization: empty vector
 */
void init_yval_vector(yval_vector_t *v) {
  v->capacity = 0;
  v->size = 0;
  v->data = NULL;
}

/*
 * Extend: increase the vector's capacity
 */
static void extend_yval_vector(yval_vector_t *v) {
  uint32_t n;

  n = v->capacity;
  if (n == 0) {
    n = DEF_YVAL_VECTOR_SIZE;
  } else {
    n ++;
    n += (n >> 1);
    if (n >= MAX_YVAL_VECTOR_SIZE) {
      out_of_memory();
    }
  }
  v->data = (yval_t *) safe_realloc(v->data, n * sizeof(yval_t));
  v->capacity = n;
}
 
/*
 * Add pair (id, tag) at the end of v
 */
void yval_vector_push(yval_vector_t *v, int32_t id, yval_tag_t tag) {
  uint32_t i;

  i = v->size;
  if (i == v->capacity) {
    extend_yval_vector(v);
  }
  assert(i < v->capacity);
  v->data[i].node_id = id;
  v->data[i].node_tag = tag;
  v->size = i + 1;
}

/*
 * Empty the vector
 */
void reset_yval_vector(yval_vector_t *v) {
  v->size = 0;
  if (v->capacity > YVAL_VECTOR_REDUCE_THRESHOLD) {
    safe_free(v->data);
    v->data = NULL;
    v->capacity = 0;
  }
}

/*
 * Delete
 */
void delete_yval_vector(yval_vector_t *v) {
  safe_free(v->data);
  v->data = NULL;
}


/*
 * TAGS
 */

/*
 * Conversion of value_kind_t to yval_tag_t
 */
static const yval_tag_t val_kind2tag[NUM_VALUE_KIND] = {
  YVAL_UNKNOWN,    // UNKNOWN_VALUE
  YVAL_BOOL,       // BOOLEAN_VALUE
  YVAL_RATIONAL,   // RATIONAL_VALUE
  YVAL_BV,         // BITVECTOR_VALUE
  YVAL_TUPLE,      // TUPPLE_VALUE
  YVAL_SCALAR,     // UNINTERPRETED_VALUE
  YVAL_FUNCTION,   // FUNCTION_VALUE
  YVAL_MAPPING,    // MAP_VALUE
  YVAL_FUNCTION,   // UPDATE_VALUE
};

yval_tag_t tag_for_valkind(value_kind_t kind) {
  return val_kind2tag[kind];
}


/*
 * DESCRIPTORS FOR VALUES
 */

/*
 * Build a yval_t descriptor for value v defined in tbl
 * - v must be a valid index in tbl
 */
void get_yval(value_table_t *tbl, value_t v, yval_t *d) {
  assert(good_object(tbl, v));
  d->node_id = v;
  d->node_tag = tag_for_valkind(object_kind(tbl, v));
}


/*
 * Expand a tuple v:
 * - a must be an array large enough to store n values where n = arity of v
 */
void yval_expand_tuple(value_table_t *tbl, value_t v, yval_t *a) {
  value_tuple_t *tuple;
  uint32_t i, n;

  tuple = vtbl_tuple(tbl, v);
  n = tuple->nelems;
  for (i=0; i<n; i++) {
    get_yval(tbl, tuple->elem[i], a + i);
  }
}


/*
 * Expand a mapping m:
 * - a must be an array large enough to store n values where n = arity of m
 * - the domain of m is stored in a[0 ... n-1] and the value is stored in *v
 * (i.e., m is of the form [a_0 ... a_n-1 -> v])
 */
void yval_expand_mapping(value_table_t *tbl, value_t m, yval_t *a, yval_t *v) {
  value_map_t *map;
  uint32_t i, n;

  map = vtbl_map(tbl, m);
  n = map->arity;
  get_yval(tbl, map->val, v);
  for (i=0; i<n; i++) {
    get_yval(tbl, map->arg[i], a + i);
  }
}


/*
 * Expand function f
 */
void yval_expand_function(value_table_t *tbl, value_t f, yval_vector_t *v, yval_t *def) {
  value_fun_t *fun;
  uint32_t i, n;
  value_t x;

  reset_yval_vector(v);

  fun = vtbl_function(tbl, f);
  get_yval(tbl, fun->def, def);
  n = fun->map_size;
  for (i=0; i<n; i++) {
    x = fun->map[i];
    assert(object_is_map(tbl, x));
    yval_vector_push(v, x, YVAL_MAPPING);
  }
}


/*
 * Expand update object f
 */
void yval_expand_update(value_table_t *tbl, value_t f, yval_vector_t *v, yval_t *def) {
  map_hset_t *hset;
  value_t x;
  type_t tau;
  uint32_t i, n;

  // build the mapping for f into tbl->hset1
  // get the default value in x
  vtbl_expand_update(tbl, f, &x, &tau);
  get_yval(tbl, x, def);

  reset_yval_vector(v);

  hset = tbl->hset1;
  assert(hset != NULL);
  n = hset->nelems;
  for (i=0; i<n; i++) {
    x = hset->data[i];
    assert(object_is_map(tbl, x));
    yval_vector_push(v, x, YVAL_MAPPING);
  }
}

