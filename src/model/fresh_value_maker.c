/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */


/*
 * SUPPORT FOR CONSTRUCTING FRESH CONCRETE VALUES
 */

#include <assert.h>

#include "model/fresh_value_maker.h"
#include "utils/memalloc.h"


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
  init_bvconstant(&maker->aux);
  maker->int_count = 0;
}


/*
 * Delete everything
 */
void delete_fresh_val_maker(fresh_val_maker_t *maker) {
  delete_tup_counter_vector(&maker->tuples);
  delete_bv_counter_vector(&maker->bvs);
  delete_bvconstant(&maker->aux);
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

  if (n <= 64) {
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

  } else {
    // large bitsize: can't use test_bv64
    x = maker->bvs.data[i].count;
    while (x < max) {
      bvconstant_copy64(&maker->aux, n, (uint64_t) x);
      if (vtbl_test_bvconstant(maker->vtbl, &maker->aux)) break;
      x ++;
    }
    if (x < max) {
      v = vtbl_mk_bv_from_constant(maker->vtbl, &maker->aux);
      maker->bvs.data[i].count = x + 1;
    } else {
      v = null_value;
      maker->bvs.data[i].count = x;
    }
  }

  return v;
}

/*
 * FRESH TUPLES
 */

/*
 * Set a[i] to an arbitrary element of type tau[i]
 * - skip j
 */
static void fill_tuple(value_table_t *vtbl, uint32_t n, type_t *tau, value_t *a, uint32_t j) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (i != j) {
      a[i] = vtbl_make_object(vtbl, tau[i]);
    }
  }
}

/*
 * Try to generate a fresh tuple of n values
 * - tau[i] = type for a[i]
 * - return false if this fails
 */
static bool gen_fresh_tuple(fresh_val_maker_t *maker, uint32_t n, type_t *tau, value_t *a) {
  type_table_t *types;
  value_table_t *vtbl;
  tuple_counter_t *ctr;
  uint32_t j;
  value_t v;

  types = maker->types;
  vtbl = maker->vtbl;

  // search for an infinite tau[j]
  for (j=0; j<n; j++) {
    if (! is_finite_type(types, tau[j])) {
      break;
    }
  }

  if (j < n) {
    // tau[j] is infinite
    fill_tuple(vtbl, n, tau, a, j);
    a[j] = make_fresh_value(maker, tau[j]);
    return true;
  }

  // all types are finite: try to get a fresh element
  // for one of tau[j]
  for (j=0; j<n; j++) {
    v = make_fresh_value(maker, tau[j]);
    if (v != null_value) break;
  }

  if (j < n) {
    // we have a fresh v of type tau[j]
    fill_tuple(vtbl, n, tau, a, j);
    a[j] = v;
    return true;
  }

  // all tau[i] are finite and saturated: use the counter
  ctr = get_tuple_counter(maker, n, tau);
  j = ctr->count;
  while (j < ctr->card && vtbl_test_object_tuple(vtbl, n, tau, j)) {
    j++;
  }
  if (j < ctr->card) {
    vtbl_gen_object_tuple(vtbl, n, tau, j, a);
    ctr->count = j+1;
    return true;
  }

  // failed
  ctr->count = j;
  return false;
}


value_t make_fresh_tuple(fresh_val_maker_t *maker, type_t tau) {
  value_t buffer[10];
  value_t *aux;
  tuple_type_t *d;
  uint32_t n;
  value_t v;

  d = tuple_type_desc(maker->types, tau);

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


/*
 * FRESH FUNCTIONS
 */

value_t make_fresh_function(fresh_val_maker_t *maker, type_t tau) {
  value_t buffer[10];
  value_t a[2];
  value_t *aux;
  type_table_t *types;
  value_table_t *vtbl;
  function_type_t *d;
  tuple_counter_t *ctr;
  type_t sigma;
  value_t v;
  uint32_t i, n;

  types = maker->types;
  vtbl = maker->vtbl;

  d = function_type_desc(types, tau);;
  sigma = d->range;

  if (is_unit_type(types, sigma)) {
    // sigma is a singleton so there's only one function of type tau
    v = null_value;
    if (! vtbl_test_object(vtbl, tau, 0)) {
      v = vtbl_gen_object(vtbl, tau, 0);
    }
    return v;
  }

  // try to get a fresh value of type sigma
  // if this works create a new constant function
  v = make_fresh_value(maker, sigma);
  if (v != null_value) {
    v = vtbl_mk_function(vtbl, tau, 0, NULL, v);
    return v;
  }

  // sigma is finite and saturated
  v = null_value;
  if (card_of_domain_type(types, tau) > 2) {
    // try to get a fresh tuple in the domain
    n = d->ndom; // function arity
    aux = buffer;
    if (n > 10) {
      assert(n < UINT32_MAX/sizeof(value_t));
      aux = (value_t *) safe_malloc(n * sizeof(value_t));
    }

    if (gen_fresh_tuple(maker, n, d->domain, aux)) {
      /*
       * We have a fresh tuple aux[0 ... n-1].
       * We get two objects a[0] and a[1] of type sigma
       * and return the function f that maps every thing to a[0]
       * except aux[0 .. n-1] that's mapped a[1].
       * This f must be fresh.
       *
       * Take another g of type tau. Since aux is fresh,
       * then g(aux) is the default value for g.
       * - if g's default is not a[1], then g /= f
       * - if g's default is a[1] and there's an x /= aux such
       *   that g(x) = a[1] then g /= f (since f(x) = a[0]).
       * - otherwise,
       *   - the default for g is a[1]
       *   - for any other x in the domain g(x) /= a[1]
       *   - by construction, the default value for g is
       *     one that occurs most often in the range of g
       *     so g(x) /= g(y) whenever x /= y.
       *   - since the domain has cardinality > 2, there's
       *     a y such that g(y) /= a[0] and g(y) /= a[1] so g /= f
       *     in that case too.
       */
      if (! vtbl_make_two_objects(vtbl, sigma, a)) {
	assert(false); // should never happen
      }
      v = vtbl_mk_map(vtbl, n, aux, a[1]); // map (aux[0] ... aux[n-1] := a[1]);
      v = vtbl_mk_function(vtbl, tau, 1, &v, a[0]);
    }

    if (n > 10) {
      safe_free(aux);
    }
  }

  if (v == null_value) {
    /*
     * The previous trick has failed:
     * - sigma and tau[0 ... n-1] are all finite
     * - sigma and tau[0] x ... x tau[n-1] are saturated
     * Try the counter for tau
     */
    ctr = get_type_counter(maker, tau);
    i = ctr->count;
    while (i < ctr->card && vtbl_test_object(vtbl, tau, i)) {
      i ++;
    }
    if (i < ctr->card) {
      v = vtbl_gen_object(vtbl, tau, i);
      ctr->count = i+1;
    } else {
      // failed
      ctr->count = i;
      assert(v == null_value);
    }
  }

  return v;
}


/*
 * Create a fresh value of type tau:
 * - return null_value if that fails (i.e., tau is finite and all values
 *   or type tau are already present)
 */
value_t make_fresh_value(fresh_val_maker_t *maker, type_t tau) {
  type_table_t *types;
  value_t v;

  types = maker->types;

  switch (type_kind(types, tau)) {
  case BOOL_TYPE:
    v = null_value;
    break;

  case INT_TYPE:
  case REAL_TYPE:
    v = make_fresh_integer(maker);
    assert(v != null_value);
    break;

  case BITVECTOR_TYPE:
    v = make_fresh_bv(maker, bv_type_size(types, tau));
    break;

  case SCALAR_TYPE:
  case UNINTERPRETED_TYPE:
    v = make_fresh_const(maker, tau);
    break;

  case TUPLE_TYPE:
    v = make_fresh_tuple(maker, tau);
    break;

  case FUNCTION_TYPE:
    v = make_fresh_function(maker, tau);
    break;

  default:
    assert(false);
    v = null_value;
    break;
  }

  return v;
}

