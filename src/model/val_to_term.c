/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CONVERSION OF CONCRETE VALUES TO CONSTANT TERMS
 */

#include <assert.h>

#include "model/val_to_term.h"


/*
 * Initialize a converter structure:
 * - vtbl = table of values
 * - term = term table
 */
void init_val_converter(val_converter_t *convert, value_table_t *vtbl, term_table_t *terms) {
  convert->vtbl = vtbl;
  convert->terms = terms;

  init_int_hmap(&convert->cache, 0); // default hmap size
  init_istack(&convert->stack);
  // conver->env not initialized
}


/*
 * Delete cache and stack
 */
void delete_val_converter(val_converter_t *convert) {
  convert->vtbl = NULL;
  convert->terms = NULL;
  delete_int_hmap(&convert->cache);
  delete_istack(&convert->stack);
}


/*
 * Reset cache and stack
 */
void reset_val_converter(val_converter_t *convert) {
  int_hmap_reset(&convert->cache);
  reset_istack(&convert->stack);
}


/*
 * Conversion of primitive terms
 */
static term_t convert_bool(value_table_t *vtbl, value_t v) {
  return bool2term(boolobj_value(vtbl, v));
}

static term_t convert_rational(term_table_t *terms, value_table_t *vtbl, value_t v) {
  return arith_constant(terms, vtbl_rational(vtbl, v));
}

static term_t convert_bitvector(term_table_t *terms, value_table_t *vtbl, value_t v) {
  value_bv_t *b;
  uint64_t x;
  uint32_t n;
  term_t t;

  b = vtbl_bitvector(vtbl, v);
  n = b->nbits;
  assert(n > 0);

  if (n <= 64) {
    x = b->data[0];
    if (n > 32) {
      x |= ((uint64_t) b->data[1]) << 32;
    }
    t = bv64_constant(terms, n, x);
  } else {
    t = bvconst_term(terms, n, b->data);
  }

  return t;
}

static term_t convert_unint(term_table_t *terms, value_table_t *vtbl, value_t v) {
  value_unint_t *u;

  u = vtbl_unint(vtbl, v);
  return constant_term(terms, u->type, u->index);
}


/*
 * Attempt to convert a primitive value v
 * - return an error code if v is not primitive
 */
term_t convert_simple_value(term_table_t *terms, value_table_t *vtbl, value_t v) {
  term_t t;

  switch (object_kind(vtbl, v)) {
  case UNKNOWN_VALUE:
    t = CONVERT_UNKNOWN_VALUE;
    break;

  case BOOLEAN_VALUE:
    t = convert_bool(vtbl, v);
    break;

  case RATIONAL_VALUE:
    t = convert_rational(terms, vtbl, v);
    break;

  case BITVECTOR_VALUE:
    t = convert_bitvector(terms, vtbl, v);
    break;

  case TUPLE_VALUE:
    t = CONVERT_NOT_PRIMITIVE;
    break;

  case UNINTERPRETED_VALUE:
    t = convert_unint(terms, vtbl, v);
    break;

  case FUNCTION_VALUE:
  case UPDATE_VALUE:
    t = CONVERT_FUNCTION;
    break;

  case MAP_VALUE:
    t = CONVERT_FAILED;
    break;

  default:
    t = CONVERT_INTERNAL_ERROR;
    assert(false);
    break;
  }

  return t;
}



/*
 * Check what's mapped to v in convert->cache
 * - return -1 if nothing
 */
static term_t convert_cached_term(val_converter_t *convert, value_t v) {
  int_hmap_pair_t *r;
  term_t t;

  assert(good_object(convert->vtbl, v));

  t = NULL_TERM;
  r = int_hmap_find(&convert->cache, v);
  if (r != NULL) {
    t = r->val;
  }

  return t;
}


/*
 * Store the mapping [v --> t] in the cache
 */
static void convert_cache_map(val_converter_t *convert, value_t v, term_t t) {
  int_hmap_pair_t *r;

  assert(good_object(convert->vtbl, v) && good_term(convert->terms, t));

  r = int_hmap_get(&convert->cache, v);
  assert(r->val < 0);
  r->val = t;
}


/*
 * Recursive conversion of primitive and tuple terms
 * - raise an exception via longjmp if the conversion fails.
 */
static term_t convert_val(val_converter_t *convert, value_t v);

/*
 * Convert a tuple
 */
static term_t convert_tuple(val_converter_t *convert, value_tuple_t *tup) {
  uint32_t i, n;
  term_t *a;
  term_t t;

  n = tup->nelems;
  a = alloc_istack_array(&convert->stack, n);
  for (i=0; i<n; i++) {
    a[i] = convert_val(convert, tup->elem[i]);
  }
  t = tuple_term(convert->terms, n, a);

  free_istack_array(&convert->stack, a);

  return t;
}



/*
 * Mapping from object kind to error code
 * - code < 0 means that object kind can't be converted (error)
 * - code == 0 means that we can try
 */
static const int32_t convert_code[NUM_VALUE_KIND] = {
  CONVERT_UNKNOWN_VALUE,  // UNKNOWN_VALUE
  0,                      // BOOLEAN_VALUE
  0,                      // RATIONAL_VALUE
  0,                      // BITVECTOR_VALUE
  0,                      // TUPLE_VALUE
  0,                      // UNINTERPRETED_VALUE
  CONVERT_FUNCTION,       // FUNCTION_VALUE
  CONVERT_FAILED,         // MAP_VALUE
  CONVERT_FUNCTION,       // UPDATE_VALUE
};

static inline int32_t get_convert_code(value_kind_t k) {
  assert(k >= 0);
  return (k < NUM_VALUE_KIND) ? convert_code[k] : CONVERT_INTERNAL_ERROR;
}

static term_t convert_val(val_converter_t *convert, value_t v) {
  value_table_t *vtbl;
  value_kind_t kind;
  int32_t c;
  term_t t;

  vtbl = convert->vtbl;
  kind = object_kind(vtbl, v);

  switch (kind) {
  case BOOLEAN_VALUE:
    // skip the cache for Boolean values
    t = convert_bool(vtbl, v);
    break;

  case RATIONAL_VALUE:
    t = convert_cached_term(convert, v);
    if (t < 0) {
      t = convert_rational(convert->terms, vtbl, v);
      convert_cache_map(convert, v, t);
    }
    break;

  case BITVECTOR_VALUE:
    t = convert_cached_term(convert, v);
    if (t < 0) {
      t = convert_bitvector(convert->terms, vtbl, v);
      convert_cache_map(convert, v, t);
    }
    break;

  case TUPLE_VALUE:
    t = convert_cached_term(convert, v);
    if (t < 0) {
      t = convert_tuple(convert, vtbl_tuple(vtbl, v));
      convert_cache_map(convert, v, t);
    }
    break;

  case UNINTERPRETED_VALUE:
    t = convert_cached_term(convert, v);
    if (t < 0) {
      t = convert_unint(convert->terms, vtbl, v);
      convert_cache_map(convert, v, t);
    }
    break;

  default:
    c = get_convert_code(kind);
    assert(c < 0);
    longjmp(convert->env, c);
    break;
  }

  return t;
}


/*
 * Top level: setup the jmp buffer then call the recursive function
 */
term_t convert_value(val_converter_t *convert, value_t v) {
  term_t t;

  t = setjmp(convert->env);
  if (t == 0) {
    t = convert_val(convert, v);
  } else {
    // exception
    assert(t < 0);
    reset_istack(&convert->stack);
  }

  return t;
}
