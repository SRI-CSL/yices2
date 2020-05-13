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
 * Computation of the free variables of a term.
 */

#include <assert.h>

#include "terms/free_var_collector.h"


/*
 * Initialization
 */
void init_fvar_collector(fvar_collector_t *collect, term_table_t *ttbl) {
  collect->terms = ttbl;
  init_ptr_hmap(&collect->map, 0);         // default size
  init_harray_store(&collect->store);
  init_pstack(&collect->stack);
}


/*
 * Delete the whole thing
 */
void delete_fvar_collector(fvar_collector_t *collect) {
  delete_ptr_hmap(&collect->map);
  delete_harray_store(&collect->store);
  delete_pstack(&collect->stack);
}


/*
 * Reset: empty everything
 */
void reset_fvar_collector(fvar_collector_t *collect) {
  ptr_hmap_reset(&collect->map);
  reset_harray_store(&collect->store);
  reset_pstack(&collect->stack);
}



/*
 * For debugging: check that a is sorted and does not contain duplicates
 * and that all elements of a are variables.
 */
#ifndef NDEBUG
static bool good_var_set(term_table_t *terms, harray_t *a) {
  uint32_t i, n;
  term_t x;

  n = a->nelems;
  x = NULL_TERM; // -1
  for (i = 0; i<n; i++) {
    if (a->data[i] <= x) return false; // not sorted or duplicate
    x = a->data[i];
    if (term_kind(terms, x) != VARIABLE) return false;
  }

  return true;
}

#endif


/*
 * Empty set of variables
 */
static inline harray_t *empty_fvar_set(fvar_collector_t *collect) {
  return empty_harray(&collect->store);
}


/*
 * Singleton set: x = unique element
 */
static inline harray_t *singleton_fvar_set(fvar_collector_t *collect, term_t x) {
  return singleton_harray(&collect->store, x);
}



/*
 * Check whether the free var set for term index i is in the hash map
 * - return NULL if it's not
 */
static harray_t *lookup_free_vars(fvar_collector_t *collect, int32_t i) {
  ptr_hmap_pair_t *p;
  harray_t *a;

  a = NULL;
  p = ptr_hmap_find(&collect->map, i);
  if (p != NULL) {
    a = p->val;
    assert(a != NULL && good_var_set(collect->terms, a));
  }
  return a;
}


/*
 * Store the free var set of i into the hash map
 * - i: term index
 * - a: set of variables of i
 * There must not be anything mapped to i the the map yet.
 */
static void cache_free_vars(fvar_collector_t *collect, int32_t i, harray_t *a) {
  ptr_hmap_pair_t *p;

  p = ptr_hmap_get(&collect->map, i);
  assert(p->val == NULL);
  p->val = a;
}


/*
 * Free variables in composite terms (other than forall)
 */
static harray_t *free_vars_of_composite(fvar_collector_t *collect, composite_term_t *c) {
  harray_t **a;
  harray_t *result;
  uint32_t i, n;

  n = c->arity;
  a = (harray_t **) alloc_pstack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_free_vars_of_term(collect, c->arg[i]);
  }
  result = merge_harrays(&collect->store, a, n);
  free_pstack_array(&collect->stack, (void **) a);

  return result;
}

static harray_t *free_vars_of_pprod(fvar_collector_t *collect, pprod_t *p) {
  harray_t **a;
  harray_t *result;
  uint32_t i, n;

  n = p->len;
  a = (harray_t **) alloc_pstack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_free_vars_of_term(collect, p->prod[i].var);
  }
  result = merge_harrays(&collect->store, a, n);
  free_pstack_array(&collect->stack, (void **) a);

  return result;
}

static harray_t *free_vars_of_poly(fvar_collector_t *collect, polynomial_t *p) {
  harray_t **a;
  harray_t *result;
  monomial_t *mono;
  uint32_t i, n;

  n = p->nterms;
  mono = p->mono;
  // skip the constant term if any
  if (mono[0].var == const_idx) {
    n --;
    mono ++;
  }

  a = (harray_t **) alloc_pstack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_free_vars_of_term(collect, mono[i].var);
  }
  result = merge_harrays(&collect->store, a, n);
  free_pstack_array(&collect->stack, (void **) a);

  return result;
}

static harray_t *free_vars_of_bvpoly64(fvar_collector_t *collect, bvpoly64_t *p) {
  harray_t **a;
  harray_t *result;
  bvmono64_t *mono;
  uint32_t i, n;

  n = p->nterms;
  mono = p->mono;
  if (mono[0].var == const_idx) {
    n--;
    mono ++;
  }
  a = (harray_t **) alloc_pstack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_free_vars_of_term(collect, mono[i].var);
  }
  result = merge_harrays(&collect->store, a, n);
  free_pstack_array(&collect->stack, (void **) a);

  return result;
}

static harray_t *free_vars_of_bvpoly(fvar_collector_t *collect, bvpoly_t *p) {
  harray_t **a;
  harray_t *result;
  bvmono_t *mono;
  uint32_t i, n;

  n = p->nterms;
  mono = p->mono;
  if (mono[0].var == const_idx) {
    n--;
    mono ++;
  }

  a = (harray_t **) alloc_pstack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_free_vars_of_term(collect, mono[i].var);
  }
  result = merge_harrays(&collect->store, a, n);
  free_pstack_array(&collect->stack, (void **) a);

  return result;
}


/*
 * Free variables in (FORALL x1, ..., xn: P) and (LAMBDA x1 ... x_n : t)
 */
static harray_t *free_vars_of_binding(fvar_collector_t *collect, composite_term_t *p) {
  harray_t *a;
  uint32_t n;

  n = p->arity;
  /*
   * The bound variables are p->arg[0] to p->arg[n-2]
   * The body is p->arg[n-1]
   */
  assert(n >= 2);
  a = get_free_vars_of_term(collect, p->arg[n-1]);
  a = harray_remove_elem(&collect->store, a, n-1, p->arg);

  return a;
}


/*
 * Free variables in a root atom r:
 */
static harray_t *free_vars_of_root_atom(fvar_collector_t *collect, root_atom_t *r) {
  harray_t *a;
  term_t x;

  x = r->x;
  a  = get_free_vars_of_term(collect, r->p);  // p = polynomial
  a = harray_remove_elem(&collect->store, a, 1, &x); // x = bound variable in p(x, ...)

  return a;
}



/*
 * Compute the set of free variables in term t:
 * - t must be defined in collect->terms
 * - the set is returned as a harray structure a (cf. int_array_hsets)
 *   a->nelems = size of the set = n
 *   a->data[0 ... n-1] = variables of t listed in increasing order
 */
harray_t *get_free_vars_of_term(fvar_collector_t *collect, term_t t) {
  term_table_t *terms;
  harray_t *result;
  int32_t i;

  terms = collect->terms;
  i = index_of(t);
  switch (kind_for_idx(terms, i)) {
  case CONSTANT_TERM:
  case ARITH_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
  case UNINTERPRETED_TERM:
    result = empty_fvar_set(collect);
    break;

  case VARIABLE:
    // we use pos_term(i) rather than t since t could be a negative term
    // (i.e., neg_term(i) that represents (not v) for some Boolean variable v)
    result = singleton_fvar_set(collect, pos_term(i));
    break;

  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
  case ARITH_IS_INT_ATOM:
  case ARITH_FLOOR:
  case ARITH_CEIL:
  case ARITH_ABS:
    result = get_free_vars_of_term(collect, integer_value_for_idx(terms, i));
    break;

  case ARITH_ROOT_ATOM:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_root_atom(collect, root_atom_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
  case APP_TERM:
  case UPDATE_TERM:
  case TUPLE_TERM:
  case EQ_TERM:
  case DISTINCT_TERM:
  case OR_TERM:
  case XOR_TERM:
  case ARITH_BINEQ_ATOM:
  case ARITH_RDIV:
  case ARITH_IDIV:
  case ARITH_MOD:
  case ARITH_DIVIDES_ATOM:
  case BV_ARRAY:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_composite(collect, composite_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  case FORALL_TERM:
  case LAMBDA_TERM:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_binding(collect, composite_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  case SELECT_TERM:
  case BIT_TERM:
    result = get_free_vars_of_term(collect, select_for_idx(terms, i)->arg);
    break;

  case POWER_PRODUCT:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_pprod(collect, pprod_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  case ARITH_POLY:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_poly(collect, polynomial_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  case BV64_POLY:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_bvpoly64(collect, bvpoly64_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  case BV_POLY:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_bvpoly(collect, bvpoly_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  default:
    assert(false);
    result = NULL;
    break;
  }

  return result;
}



/*
 * Check whether t is a ground term:
 * - side effect: this computes the set of free variables of t
 */
bool term_is_ground(fvar_collector_t *collect, term_t t) {
  harray_t *a;

  a = get_free_vars_of_term(collect, t);
  return a->nelems == 0;
}


/*
 * Filter for ptr_hmap: r is a pair <term, ptr>
 * - r must be deleted if the term is dead
 * - aux is a pointer to the term table
 */
static bool fvar_dead_hmap_pair(void *aux, const ptr_hmap_pair_t *r) {
  return !live_term(aux, r->key);
}


/*
 * Filter for the store:
 * - a is a harray structure
 * - aux is a pointer to the term table
 * - a must be deleted if it contains a dead term
 */
static bool fvar_dead_harray(void *aux, const harray_t *a) {
  uint32_t i, n;

  n = a->nelems;
  for (i=0; i<n; i++) {
    if (!live_term(aux, a->data[i])) {
      return true;
    }
  }

  return false;
}



/*
 * Cleanup: remove any references to deleted terms
 * - this must be called after terms are removed from collect->terms
 */
void cleanup_fvar_collector(fvar_collector_t *collect) {
  // must delete records in the map first
  ptr_hmap_remove_records(&collect->map, collect->terms, fvar_dead_hmap_pair);
  harray_store_remove_arrays(&collect->store, collect->terms, fvar_dead_harray);
}
