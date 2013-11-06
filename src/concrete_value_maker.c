/*
 * Build values of some type
 */

#include <assert.h>

#include "concrete_value_maker.h"


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
value_t vtbl_make_object(value_table_t *vtbl, type_t tau) {
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
bool vtbl_make_two_objects(value_table_t *vtbl, type_t tau, value_t a[2]) {
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
