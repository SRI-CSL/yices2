/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CONVERSION OF CONSTANT TERMS TO CONCRETE VALUES
 */

#include <assert.h>

#include "model/term_to_val.h"

/*
 * Initialize for terms + vtbl
 */
void init_term_converter(term_converter_t *convert, term_table_t *terms, value_table_t *vtbl) {
  convert->terms = terms;
  convert->vtbl = vtbl;
  init_int_hmap(&convert->cache, 0);
  init_istack(&convert->stack);
}


/*
 * Delete
 */
void delete_term_converter(term_converter_t *convert) {
  convert->terms = NULL;
  convert->vtbl = NULL;
  delete_int_hmap(&convert->cache);
  delete_istack(&convert->stack);
}


/*
 * Reset cache and stack
 */
void reset_term_converter(term_converter_t *convert) {
  int_hmap_reset(&convert->cache);
  reset_istack(&convert->stack);
}

/*
 * Check what's mapped to t in convert->cache
 * - return -1 (null_value) if t is not in the cache
 */
static value_t convert_cached_value(term_converter_t *convert, term_t t) {
  int_hmap_pair_t *r;
  value_t v;

  assert(good_term(convert->terms, t));

  v = null_value;
  r = int_hmap_find(&convert->cache, t);
  if (r != NULL) {
    v = r->val;
  }

  return v;
}


/*
 * Store the mapping [t --> v] in the cache
 */
static void term_convert_cache(term_converter_t *convert, term_t t, value_t v) {
  int_hmap_pair_t *r;

  assert(good_term(convert->terms, t) && good_object(convert->vtbl, v));

  r = int_hmap_get(&convert->cache, t);
  assert(r->val < 0);
  r->val = v;
}


/*
 * Convert bitvector constants
 */
static value_t term_to_bv64_constant(term_converter_t *convert, bvconst64_term_t *d) {
  return vtbl_mk_bv_from_bv64(convert->vtbl, d->bitsize, d->value);
}

static value_t term_to_bv_constant(term_converter_t *convert, bvconst_term_t *d) {
  return vtbl_mk_bv_from_bv(convert->vtbl, d->bitsize, d->data);
}


/*
 * Recursive function: convert t to a concrete value
 * - raise an exception (via longjmp) of t can't be converted
 */
static value_t term_to_val(term_converter_t *convert, term_t t);

/*
 * Conversion for a tuple tup
 */
static value_t term_to_tuple(term_converter_t *convert, composite_term_t *tuple) {
  uint32_t i, n;
  value_t *a;
  value_t v;

  n = tuple->arity;
  a = alloc_istack_array(&convert->stack, n);
  for (i=0; i<n; i++) {
    a[i] = term_to_val(convert, tuple->arg[i]);
  }
  v = vtbl_mk_tuple(convert->vtbl, n, a);
  free_istack_array(&convert->stack, a);

  return v;
}

/*
 * Convert term t to a concrete value
 */
static value_t term_to_val(term_converter_t *convert, term_t t) {
  term_table_t *terms;
  value_t v;

  terms = convert->terms;
  assert(good_term(terms, t));

  switch (term_kind(terms, t)) {
  case UNUSED_TERM:
  case RESERVED_TERM:
    longjmp(convert->env, TERM2VAL_INTERNAL_ERROR);
    break;

  case CONSTANT_TERM:
    if (t == true_term) {
      v = vtbl_mk_true(convert->vtbl);
    } else if (t == false_term) {
      v = vtbl_mk_false(convert->vtbl);
    } else {
      v = vtbl_mk_const(convert->vtbl, term_type(terms, t), constant_term_index(terms, t), term_name(terms, t));
    }
    break;

  case ARITH_CONSTANT:
    v = vtbl_mk_rational(convert->vtbl, rational_term_desc(terms, t));
    break;

  case BV64_CONSTANT:
    v = term_to_bv64_constant(convert, bvconst64_term_desc(terms, t));
    break;

  case BV_CONSTANT:
    v = term_to_bv_constant(convert, bvconst_term_desc(terms, t));
    break;

  case TUPLE_TERM:
    v = convert_cached_value(convert, t);
    if (v < 0) {
      v = term_to_tuple(convert, tuple_term_desc(terms, t));
      term_convert_cache(convert, t, v);
    }
    break;

  default:
    longjmp(convert->env, TERM2VAL_NOT_CONSTANT);
    break;
  }

  return v;
}

/*
 * Convert term t to a concrete value
 * - t must be a valid term
 * - return a negative code if the conversion fails
 */
value_t convert_term_to_val(term_converter_t *convert, term_t t) {
  value_t v;

  v = setjmp(convert->env);
  if (v == 0) {
    v = term_to_val(convert, t);
  } else {
    // exception
    assert(v < 0);
    reset_istack(&convert->stack);
  }

  return v;
}
