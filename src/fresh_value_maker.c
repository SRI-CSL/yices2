/*
 * SUPPORT FOR CONSTRUCTING FRESH CONCRETE VALUES
 */

#include <assert.h>

#include "memalloc.h"
#include "fresh_value_maker.h"


/*
 * TUPLE COUNTERS
 */

/*
 * Allocate and initialize a new counter for tau[0 ... n-1]
 * - types = the type table
 */
static tuple_counter_t *new_tuple_counter(type_table_t *types, uint32_t n, type_t *tau) {
  tuple_counter_t *tmp;
  uint32_t i;

  if (n > MAX_TUPLE_COUNTER_ARITY) {
    out_of_memory();
  }

  tmp = (tuple_counter_t *) safe_malloc(sizeof(tuple_counter_t) + n * sizeof(type_t));
  tmp->arity = n;
  tmp->card = card_of_type_product(types, n, tau);
  tmp->count = 0;

  for (i=0; i<n; i++) {
    tmp->tau[i] = tau[i];
  }

  return tmp;
}

// same thing for a single type tau
static tuple_counter_t *new_type_counter(type_table_t *types, type_t tau) {
  tuple_counter_t *tmp;

  tmp = (tuple_counter_t *) safe_malloc(sizeof(tuple_counter_t) + sizeof(type_t));
  tmp->arity = 1;
  tmp->card = type_card(types, tau);
  tmp->count = 0;
  tmp->tau[0] = tau;

  return tmp;
}


/*
 * Check whether r matches tau[0 ... n-1]
 */
static bool counter_matches_tuple(tuple_counter_t *r, uint32_t n, type_t *tau) {
  uint32_t i;

  if (n != r->arity) {
    return false;
  }

  for (i=0; i<n; i++) {
    if (tau[i] != r->tau[i]) {
      return false;
    }
  }

  return true;
}

// variant for a single type tau
static bool counter_matches_type(tuple_counter_t *r, type_t tau) {
  return r->arity == 1 && r->tau[0] == tau;
}


/*
 * VECTOR OF TUPLE COUNTERS
 */

/*
 * Initialize: nothing allocated yet
 */
static void init_tup_counter_vector(tup_counter_vector_t *v) {
  v->data = NULL;
  v->nelems = 0;
  v->size = 0;
}

/*
 * Delete the vector and all its elements
 */
static void delete_tup_counter_vector(tup_counter_vector_t *v) {
  uint32_t i, n;

  n = v->nelems;
  if (n > 0) {
    for (i=0; i<n; i++) {
      safe_free(v->data[i]);
    }
    safe_free(v->data);
    v->data = NULL;
  }
}

/*
 * Increase the size
 */
static void extend_tup_counter_vector(tup_counter_vector_t *v) {
  uint32_t n;

  n = v->size;
  if (n == 0) {
    // first allocation: use the default size
    n = TUPLE_COUNTER_VECTOR_DEF_SIZE;
    assert(n <= TUPLE_COUNTER_VECTOR_MAX_SIZE);
    v->data = (tuple_counter_t **) safe_malloc(n * sizeof(tuple_counter_t *));
    v->size = n;
  } else {
    // try to double the size
    n <<= 1;
    if (n > TUPLE_COUNTER_VECTOR_MAX_SIZE) {
      out_of_memory();
    } 
    v->data = (tuple_counter_t **) safe_realloc(v->data, n * sizeof(tuple_counter_t*));
    v->size = n;
  }
}


/*
 * Add a record r to vector v
 */
static void add_tuple_counter(tup_counter_vector_t *v, tuple_counter_t *r) {
  uint32_t i;

  i = v->nelems;
  if (i == v->size) {
    extend_tup_counter_vector(v);
  }
  assert(i < v->size);
  v->data[i] = r;
  v->nelems = i+1;
}


/*
 * Find counter for tau[0 ... n-1]
 * - we assume v->nelems is small so we just do a linear scan
 * - return NULL if nothing found
 */
static tuple_counter_t *counter_for_tuple(tup_counter_vector_t *v, uint32_t n, type_t *tau) {
  tuple_counter_t *r;
  uint32_t i;

  for (i=0; i<v->nelems; i++) {
    r = v->data[i];
    if (counter_matches_tuple(r, n, tau)) {
      return r;
    }
  }

  return NULL;
}

// variant: for type tau
static tuple_counter_t *counter_for_type(tup_counter_vector_t *v, type_t tau) {
  tuple_counter_t *r;
  uint32_t i;

  for (i=0; i<v->nelems; i++) {
    r = v->data[i];
    if (counter_matches_type(r, tau)) {
      return r;
    }
  }

  return NULL;  
}


/*
 * BITVECTOR COUNTERS
 */

/*
 * Initialize: nothing allocated yet
 */
static void init_bv_counter_vector(bv_counter_vector_t *v) {
  v->data = NULL;
  v->nelems = 0;
  v->size = 0;
}

static void delete_bv_counter_vector(bv_counter_vector_t *v) {
  safe_free(v->data);
  v->data = NULL;
}


/*
 * Make the vector larger
 */
static void extend_bv_counter_vector(bv_counter_vector_t *v) {
  uint32_t n;

  n = v->size;
  if (n == 0) {
    // first allocation: use the default size
    n = BV_COUNTER_VECTOR_DEF_SIZE;
    assert(n <= BV_COUNTER_VECTOR_MAX_SIZE);
    v->data = (bv_counter_t *) safe_malloc(n * sizeof(bv_counter_t));
    v->size = n;
  } else {
    // double the size
    n <<= 1;
    if (n > BV_COUNTER_VECTOR_MAX_SIZE) {
      out_of_memory();
    }
    v->data = (bv_counter_t *) safe_realloc(v->data, n *sizeof(bv_counter_t));
    v->size = n;
  }
}


/*
 * Get a new counter id:
 * - initialize it for bsize = n
 */
static int32_t new_bv_counter(bv_counter_vector_t *v, uint32_t n) {
  uint32_t i;

  i = v->nelems;
  if (i == v->size) {
    extend_bv_counter_vector(v);
  }
  assert(i < v->size);

  v->data[i].bsize = n;
  v->data[i].count = 0;
  v->nelems = i+1;

  return i;
}


/*
 * Search the counter for bitvector size n
 * - return -1 if not present
 */
static int32_t counter_for_bv(bv_counter_vector_t *v, uint32_t n) {
  bv_counter_t *r;
  uint32_t i;

  assert(n > 0);
  r = v->data;
  for (i=0; i<v->nelems; i++) {
    if (r->bsize == n) {
      return i;
    }
    r ++;
  }

  return -1;
}


/*
 * MAKER STRUCTURE
 */

/*
 * Initialize the structure
 */
void init_fresh_val_maker(fresh_val_maker_t *maker, value_table_t *vtbl) {
  maker->vtbl = vtbl;
  maker->types = vtbl->type_table;
  init_tup_counter_vector(&maker->tuples);
  init_bv_counter_vector(&maker->bvs);
  maker->int_count = 0;
}


/*
 * Delete everything
 */
void delete_fresh_val_maker(fresh_val_maker_t *maker) {
  delete_tup_counter_vector(&maker->tuples);
  delete_bv_counter_vector(&maker->bvs);
}


/*
 * Search for a tuple counter.
 * If not present add a new record and return it
 */
static tuple_counter_t *get_tuple_counter(fresh_val_maker_t *maker, uint32_t n, type_t *tau) {
  tuple_counter_t *r;

  r = counter_for_tuple(&maker->tuples, n, tau);
  if (r == NULL) {
    r = new_tuple_counter(maker->types, n, tau);
    add_tuple_counter(&maker->tuples, r);    
  }

  return r;
}

// variant for type tau
static tuple_counter_t *get_type_counter(fresh_val_maker_t *maker, type_t tau) {
  tuple_counter_t *r;

  r = counter_for_type(&maker->tuples, tau);
  if (r == NULL) {
    r = new_type_counter(maker->types, tau);
    add_tuple_counter(&maker->tuples, r);
  }

  return r;
}


/*
 * Search for the counter for (bitvector n)
 * - return the index of this counter in maker->bvs
 * - create and initialize a new counter if needed
 */
static int32_t get_bv_counter(fresh_val_maker_t *maker, uint32_t n) {
  int32_t i;

  assert(n > 0);
  i = counter_for_bv(&maker->bvs, n);
  if (i < 0) {
    i = new_bv_counter(&maker->bvs, n);
  }
  assert(0 <= i && i< maker->bvs.nelems);

  return i;
}


/*
 * FRESH OBJECTS: ATOMIC TYPES
 */

/*
 * Return a fresh integer
 */
value_t make_fresh_integer(fresh_val_maker_t *maker) {
  value_t v;
  int32_t x;

  x = maker->int_count;
  while (vtbl_test_int32(maker->vtbl, x)) {
    x ++;
  }
  maker->int_count = x+1;

  v = vtbl_mk_int32(maker->vtbl, x);

  return v;
}


/*
 * Fresh constant of primitive or scalar type tau
 */
value_t make_fresh_const(fresh_val_maker_t *maker, type_t tau) {
  tuple_counter_t *r;
  uint32_t i, n;
  value_t v;

  assert(is_uninterpreted_type(maker->types, tau) || 
	 is_scalar_type(maker->types, tau));

  /*
   * If tau is uninterpreted, r->card is UINT32_MAX,
   * which is larger than the max number of object we can
   * create in maker->vtbl (so we can treat uninterpreted
   * types like scalar types).
   */
  r = get_type_counter(maker, tau);

  assert(is_scalar_type(maker->types, tau) || r->card == UINT32_MAX);

  n = r->card;
  i = r->count;
  while (i<n && vtbl_test_const(maker->vtbl, tau, i)) {
    i++;
  }
  if (i < n) {
    v = vtbl_mk_const(maker->vtbl, tau, i, NULL);
    r->count = i + 1;
  } else {
    v = null_value;
    r->count = i;
  }

  assert(is_scalar_type(maker->types, tau) || v != null_value);

  return v;
}


/*
 * Fresh constant of type (bitvector n)
 */
value_t make_fresh_bv(fresh_val_maker_t *maker, uint32_t n) {
  uint32_t x, max;
  int32_t i;
  value_t v;

  assert(0 < n);

  // max number of bitvectors of size n
  // if n>=32, we set max to UINT32_MAX = infinity

  max = UINT32_MAX;
  if (n < 32) {
    max = ((uint32_t) 1) << n;
  }

  i = get_bv_counter(maker, n);

  x = maker->bvs.data[i].count;
  while (x < max && vtbl_test_bv64(maker->vtbl, n, (uint64_t) x)) {
    x ++;
  }
  if (x < max) {
    v = vtbl_mk_bv_from_bv64(maker->vtbl, n, (uint64_t) x);
    maker->bvs.data[i].count = x + 1;
  } else {
    v = null_value;
    maker->bvs.data[i].count = x;
  }

  return v;
}


/*
 * AUXILIARY CONSTRUCTORS
 */

/*
 * Return some value of type tau: not necessarily fresh
 */
static value_t vtbl_make_object(value_table_t *vtbl, type_t tau);

/*
 * Attempt to construct two distinct objects of type tau.
 * - return true if that succeeds, false if tau is a singleton type
 * - store the two objects in a[0] and a[1]
 */
static bool vtbl_make_two_objects(value_table_t *vtbl, type_t tau, value_t a[2]);

/*
 * Tuple object for the given type
 */
static value_t vtbl_make_tuple(value_table_t *vtbl, tuple_type_t *d) {
  value_t buffer[10];
  value_t *aux;
  uint32_t i, n;
  value_t v;

  n = d->nelem;
  aux = buffer;
  if (n > 10) {
    aux = (value_t *) safe_malloc(n * sizeof(value_t));
  }

  for (i=0; i<n; i++) {
    aux[i] = vtbl_make_object(vtbl, d->elem[i]);
  }
  v = vtbl_mk_tuple(vtbl, n, aux);

  if (n > 10) {
    safe_free(aux);
  }

  return v;
}

/*
 * Return some value of type tau
 */
static value_t vtbl_make_object(value_table_t *vtbl, type_t tau) {
  type_table_t *types;
  value_t v;

  types = vtbl->type_table;

  switch (type_kind(types, tau)) {
  case BOOL_TYPE:
    v = vtbl_mk_false(vtbl);
    break;

  case INT_TYPE:
  case REAL_TYPE:
    v = vtbl_mk_int32(vtbl, 0);
    break;

  case BITVECTOR_TYPE:
    v = vtbl_mk_bv_zero(vtbl, bv_type_size(types, tau));
    break;

  case SCALAR_TYPE:
  case UNINTERPRETED_TYPE:
    v = vtbl_mk_const(vtbl, tau, 0, NULL);
    break;

  case TUPLE_TYPE:
    v = vtbl_make_tuple(vtbl, tuple_type_desc(types, tau));
    break;

  case FUNCTION_TYPE:
    v = vtbl_make_object(vtbl, function_type_range(types, tau));
    v = vtbl_mk_function(vtbl, tau, 0, NULL, v); // constant function
    break;

  default:
    assert(false);
    v = vtbl_mk_unknown(vtbl);
    break;
  }

  return v;
}



/*
 * Create two distinct tuples of the given type
 */
static bool vtbl_make_two_tuples(value_table_t *vtbl, tuple_type_t *d, value_t a[2]) {
  value_t buffer[10];
  value_t *aux;
  uint32_t i, j, n;
  bool done;

  done = false;

  n = d->nelem;
  aux = buffer;
  if (n > 10) {
    aux = (value_t *) safe_malloc(n * sizeof(value_t));
  }

  for (i=0; i<n; i++) {
    if (vtbl_make_two_objects(vtbl, d->elem[i], a)) {
      break;
    }
  }
  if (i < n) {
    // we have two elements for index i in a[0] and a[1]
    // fill in aux[0 ... n-1] except at position i
    for (j=0; j<n; j++) {
      if (j != i) {
	aux[j] = vtbl_make_object(vtbl, d->elem[j]);
      }
    }

    // first tuple: aux[i] = a[0]
    aux[i] = a[0];
    a[0] = vtbl_mk_tuple(vtbl, n, aux);
    // second tuple: aux[i] = a[1]
    aux[i] = a[1];
    a[1] = vtbl_mk_tuple(vtbl, n, aux);

    done = true;
  }
  
  if (n > 10) {
    safe_free(aux);
  }

  return done;
}


/*
 * Attempt to construct two distinct objects of type tau.
 * - return true if that succeeds, false if tau is a singleton type
 * - store the two objects in a[0] and a[1]
 */
static bool vtbl_make_two_objects(value_table_t *vtbl, type_t tau, value_t a[2]) {
  type_table_t *types;

  types = vtbl->type_table;

  switch (type_kind(types, tau)) {
  case BOOL_TYPE:
    a[0] = vtbl_mk_false(vtbl);
    a[1] = vtbl_mk_true(vtbl);
    break;

  case INT_TYPE:
  case REAL_TYPE:
    a[0] = vtbl_mk_int32(vtbl, 0);
    a[1] = vtbl_mk_int32(vtbl, 1);
    break;

  case BITVECTOR_TYPE:
    a[0] = vtbl_mk_bv_zero(vtbl, bv_type_size(types, tau));
    a[1] = vtbl_mk_bv_one(vtbl, bv_type_size(types, tau));
    break;

  case SCALAR_TYPE:
    if (is_unit_type(types, tau)) return false;
    assert(type_card(types, tau) >= 2);
    // fall-through intended

  case UNINTERPRETED_TYPE:
    a[0] = vtbl_mk_const(vtbl, tau, 0, NULL);
    a[1] = vtbl_mk_const(vtbl, tau, 1, NULL);
    break;

  case TUPLE_TYPE:
    return vtbl_make_two_tuples(vtbl, tuple_type_desc(types, tau), a);

  case FUNCTION_TYPE:
    // try to create two constant functions
    if (! vtbl_make_two_objects(vtbl, function_type_range(types, tau), a)) {
      return false;
    }
    // a[0] and a[1] are two objects of type sigma = range of tau
    a[0] = vtbl_mk_function(vtbl, tau, 0, NULL, a[0]);
    a[1] = vtbl_mk_function(vtbl, tau, 0, NULL, a[1]);
    break;
   
  default:
    assert(false);
    return false;
  }

  return true;
}


/*
 * FRESH TUPLES
 */

/*
 * Try to generate a fresh tuple of n values
 * - tau[i] = type for a[i]
 * - return false if this fails
 */
static bool gen_fresh_tuple(fresh_val_maker_t *maker, uint32_t n, type_t *tau, value_t *a) {
  return false;
}

value_t make_fresh_tuple(fresh_val_maker_t *maker, type_t tau) {
  value_t buffer[10];
  value_t *aux;
  type_table_t *types;
  tuple_type_t *d;
  uint32_t n;
  value_t v;

  types = maker->types;
  d = tuple_type_desc(types, tau);

  n = d->nelem;
  aux = buffer;
  if (n > 10) {
    assert(n <= UINT32_MAX/sizeof(value_t));
    aux = (value_t *) safe_malloc(n * sizeof(value_t));
  }

  v = null_value;
  if (gen_fresh_tuple(maker, n, d->elem, aux)) {
    v = vtbl_mk_tuple(maker->vtbl, n, aux);
  }

  if (n > 10) {
    safe_free(aux);
  }

  return v;
}
