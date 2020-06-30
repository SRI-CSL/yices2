/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
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
void init_val_converter(val_converter_t *convert, value_table_t *vtbl, term_manager_t *mgr, term_table_t *terms) {
  convert->vtbl = vtbl;
  convert->manager = mgr;
  convert->terms = terms;

  init_int_hmap(&convert->cache, 0); // default hmap size
  init_istack(&convert->stack);
  // convert->env not initialized
}


/*
 * Delete cache and stack
 */
void delete_val_converter(val_converter_t *convert) {
  convert->vtbl = NULL;
  convert->manager = NULL;
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

static term_t convert_func(val_converter_t *convert, value_table_t *table, value_t c) {
  value_fun_t *fun;
  value_map_t *mp;
  uint32_t m, n, i, j;
  term_t result;
  term_table_t *terms;
  type_table_t *types;
  function_type_t *funt;
  type_t ranget;
  term_t cond, the, rhs;
  term_t *eq;

  assert(0 <= c && c < table->nobjects && table->kind[c] == FUNCTION_VALUE);
  fun = table->desc[c].ptr;
  result = NULL_TERM;

  m = fun->arity;
  n = fun->map_size;
  i = 0;

  terms = convert->terms;
  types = terms->types;

  assert(is_function_type(types, fun->type));
  funt = function_type_desc(types, fun->type);

  ranget = funt->range;

  // first create variables for the lambda term
  term_t *vars;
  vars = (term_t *) safe_malloc(m * sizeof(term_t));

  for (j=0; j<m; j++) {
    vars[j] = new_variable(terms, funt->domain[j]);
  }

  if (n == 0) {
    // no entry in map

    if (is_unknown(table, fun->def)) {
      printf("no mapping or default value assigned to the function\n");
      assert(0);
    }
    else {
      result = convert_value(convert, fun->def);
    }
  }
  else {
    // entries present in map

    if (is_unknown(table, fun->def)) {
      // no default value, set the first mapping as the initial result

      mp = vtbl_map(table, fun->map[i]);
      assert(mp->arity == m);
      result = convert_value(convert, mp->val);

      // increment i since done with the first mapping
      i++;
    }
    else {
      // set the default value as the initial result
      result = convert_value(convert, fun->def);
    }

    if (n > 0) {
      // process the remaining mappings

      assert(m > 0);
      eq = (term_t *) safe_malloc(m * sizeof(term_t));

      for (; i<n; i++) {
        mp = vtbl_map(table, fun->map[i]);
        assert(mp->arity == m);

        for (j=0; j<m; j++) {
          rhs = convert_value(convert, mp->arg[j]);
          eq[j] = mk_eq(convert->manager, vars[j], rhs);
        }

        cond = mk_and(convert->manager, m, eq);
        the = convert_value(convert, mp->val);
        result = mk_ite(convert->manager, cond, the, result, ranget);
      }

      safe_free(eq);
    }
  }

  result = mk_lambda(convert->manager, m, vars, result);
  safe_free(vars);

  return result;
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

term_t convert_val(val_converter_t *convert, value_t v) {
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

  case FUNCTION_VALUE:
    t = convert_cached_term(convert, v);
    if (t < 0) {
      t = convert_func(convert, vtbl, v);
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



/*
 * Convert v to a constant term
 */
term_t convert_value_to_term(term_manager_t *mgr, term_table_t *terms, value_table_t *vtbl, value_t v) {
  val_converter_t convert;
  term_t t;

  t = convert_simple_value(terms, vtbl, v);
  if (t == CONVERT_NOT_PRIMITIVE) {
    init_val_converter(&convert, vtbl, mgr, terms);
    t = convert_value(&convert, v);
    delete_val_converter(&convert);
  }

  return t;
}



/*
 * In-place conversion of values b[0 ... n-1] to constant terms
 * - returns the number of values that could be successfully converted to terms
 *   (this is an integer between 0 and n).
 */
uint32_t convert_value_array(term_manager_t *mgr, term_table_t *terms, value_table_t *vtbl, uint32_t n, int32_t *b) {
  val_converter_t convert;
  uint32_t i, s;
  term_t t;

  s = 0;
  if (n > 0) {
    init_val_converter(&convert, vtbl, mgr, terms);
    for (i=0; i<n; i++) {
      t = convert_value(&convert, b[i]);
      b[i] = t;
      if (t >= 0) { // no error
	s ++;
      }
    }
    delete_val_converter(&convert);
  }

  return s;
}

