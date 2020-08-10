/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
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
 * Support of terms in a model
 */
#include <assert.h>

#include "model/model_support.h"

/*
 * Initialization: model = the relevant model
 */
void init_support_constructor(support_constructor_t *constructor, model_t *model) {
  init_evaluator(&constructor->eval, model);
  constructor->terms = model->terms;
  init_ptr_hmap(&constructor->map, 0);
  init_harray_store(&constructor->store);
  init_pstack(&constructor->stack);
}


/*
 * Deletion: free memory
 */
void delete_support_constructor(support_constructor_t *constructor) {
  delete_evaluator(&constructor->eval);
  delete_ptr_hmap(&constructor->map);
  delete_harray_store(&constructor->store);
  delete_pstack(&constructor->stack);
}



/*
 * Check whether the support set for term index i is in the hash map
 * - return NULL if it's not
 */
static harray_t *lookup_support(support_constructor_t *constructor, int32_t i) {
  ptr_hmap_pair_t *p;
  harray_t *a;

  a = NULL;
  p = ptr_hmap_find(&constructor->map, i);
  if (p != NULL) {
    a = p->val;
    assert(a != NULL);
  }
  return a;
}

/*
 * Add that a is the support set of term index i in the hash map.
 * - i: term index
 * - a: harray for this term
 * There must not be anything mapped to i already.
 */
static void cache_support(support_constructor_t *constructor, int32_t i, harray_t *a) {
  ptr_hmap_pair_t *p;

  p = ptr_hmap_get(&constructor->map, i);
  assert(p->val == NULL);
  p->val = a;
}



/*
 * Best of two support sets: a and b
 * - return the one with the smallest number of elements
 * - if a is NULL, return b.
 */
static harray_t *best_support(harray_t *a, harray_t *b) {
  assert(b != NULL);
  return (a == NULL || b->nelems < a->nelems) ? b : a;
}


/*
 * Support(t1) union Support(t2)
 */
static harray_t *merge_supports(support_constructor_t *constructor, term_t t1, term_t t2) {
  harray_t *sup1, *sup2;

  sup1 = get_term_support(constructor, t1);
  sup2 = get_term_support(constructor, t2);
  return merge_two_harrays(&constructor->store, sup1, sup2);
}


/*
 * Support for a generic composite c: no special simplification
 */
static harray_t *support_of_composite(support_constructor_t *constructor, composite_term_t *c) {
  return get_term_array_support(constructor, c->arg, c->arity);
}


/*
 * Support for an if-then-else term:
 * - ite is of the form (if c then t1 else t2)
 * - if c evaluates to true: support(ite) = support(c) U support(t1)
 *   if c evaluates to false: support(ite) = support(c) U support(t1)
 */
static harray_t *support_of_ite(support_constructor_t *constructor, composite_term_t *ite) {
  term_t c;

  assert(ite->arity == 3);

  c = ite->arg[0]; // Boolean condition
  if (eval_to_true_in_model(&constructor->eval, c)) {
    return merge_supports(constructor, c, ite->arg[1]);
  }

  if (eval_to_false_in_model(&constructor->eval, c)) {
    return merge_supports(constructor, c, ite->arg[2]);
  }

  // c can't be evaluated. it's safe to treat the if-then-else
  // like a regular composite
  return support_of_composite(constructor, ite);
}


/*
 * Support for an or term: (or t[0] ... t[n-1])
 * - if one t[i] evaluates to true, then it's sufficient for (or ... t[i] ...)
 * - if several t[i]s evaluate to true, we choose the one with smallest support
 */
static harray_t *support_of_or(support_constructor_t *constructor, composite_term_t *or) {
  harray_t *result;
  uint32_t i, n;

  result = NULL;
  n = or->arity;
  for (i=0; i<n; i++) {
    if (eval_to_true_in_model(&constructor->eval, or->arg[i])) {
      result = best_support(result, get_term_support(constructor, or->arg[i]));
    }
  }

  if (result == NULL) {
    // all sub-terms evaluate to false
    result = support_of_composite(constructor, or);
  }

  return result;
}


/*
 * Support for polynomials
 */
static harray_t *support_of_poly(support_constructor_t *constructor, polynomial_t *p) {
  harray_t **sup;
  harray_t *result;
  monomial_t *mono;
  uint32_t i, n;

  n = p->nterms;
  mono = p->mono;
  // skip the constant term if any
  if (mono[0].var == const_idx) {
    mono ++;
    n --;
  }

  sup = (harray_t **) alloc_pstack_array(&constructor->stack, n);
  for (i=0; i<n; i++) {
    sup[i] = get_term_support(constructor, mono[i].var);
  }
  result = merge_harrays(&constructor->store, sup, n);
  free_pstack_array(&constructor->stack, (void **) sup);

  return result;
}

static harray_t *support_of_bvpoly64(support_constructor_t *constructor, bvpoly64_t *p) {
  harray_t **sup;
  harray_t *result;
  bvmono64_t *mono;
  uint32_t i, n;

  n = p->nterms;
  mono = p->mono;
  // skip the constant term if any
  if (mono[0].var == const_idx) {
    mono ++;
    n --;
  }

  sup = (harray_t **) alloc_pstack_array(&constructor->stack, n);
  for (i=0; i<n; i++) {
    sup[i] = get_term_support(constructor, mono[i].var);
  }
  result = merge_harrays(&constructor->store, sup, n);
  free_pstack_array(&constructor->stack, (void **) sup);

  return result;
}

static harray_t *support_of_bvpoly(support_constructor_t *constructor, bvpoly_t *p) {
  harray_t **sup;
  harray_t *result;
  bvmono_t *mono;
  uint32_t i, n;

  n = p->nterms;
  mono = p->mono;
  // skip the constant term if any
  if (mono[0].var == const_idx) {
    mono ++;
    n --;
  }

  sup = (harray_t **) alloc_pstack_array(&constructor->stack, n);
  for (i=0; i<n; i++) {
    sup[i] = get_term_support(constructor, mono[i].var);
  }
  result = merge_harrays(&constructor->store, sup, n);
  free_pstack_array(&constructor->stack, (void **) sup);

  return result;
}


/*
 * Support for a product p
 */
static harray_t *support_of_pprod(support_constructor_t *constructor, pprod_t *p) {
  harray_t **sup;
  harray_t *result;
  uint32_t i, n;

  /*
   * first pass: if one of the terms in the product is zero
   * then that term is enough to determine the value of p
   */
  n = p->len;
  result = NULL;
  for (i=0; i<n; i++) {
    if (eval_to_zero_in_model(&constructor->eval, p->prod[i].var)) {
      result = best_support(result, get_term_support(constructor, p->prod[i].var));
    }
  }

  if (result == NULL) {
    // no zero term found: all terms in the product are relevant
    sup = (harray_t **) alloc_pstack_array(&constructor->stack, n);
    for (i=0; i<n; i++) {
      sup[i] = get_term_support(constructor, p->prod[i].var);
    }
    result = merge_harrays(&constructor->store, sup, n);
    free_pstack_array(&constructor->stack, (void **) sup);
  }
  
  return result;
}


/*
 * Support for p := (FORALL x1, ..., xn: P) or (LAMBDA x1 ... x_n : t)
 */
static harray_t *support_of_binding(support_constructor_t *constructor, composite_term_t *p) {
  harray_t *sup;
  uint32_t n;

  n = p->arity;
  /*
   * The bound variables are p->arg[0] to p->arg[n-2]
   * The body is p->arg[n-1]
   */
  assert(n >= 2);
  sup = get_term_support(constructor, p->arg[n-1]);
  sup = harray_remove_elem(&constructor->store, sup, n-1, p->arg);

  return sup;
}

/*
 * Support of a root atom r:
 */
static harray_t *support_of_root_atom(support_constructor_t *constructor, root_atom_t *r) {
  harray_t *sup;
  term_t x;

  x = r->x;
  sup = get_term_support(constructor, r->p);  // p = polynomial
  return harray_remove_elem(&constructor->store, sup, 1, &x); // x = bound variable in p(x, ...)
}


/*
 * Empty and singleton sets
 */
static inline harray_t *empty_support(support_constructor_t *constructor) {
  return empty_harray(&constructor->store);
}

static inline harray_t *singleton_support(support_constructor_t *constructore, term_t x) {
  return singleton_harray(&constructore->store, x);
}


/*
 * Get the support set of term t:
 * - t must be a valid term
 * - the support set is returned as a harray_t h
 *   h->nelems = number of terms in the set
 *   h->data[0 .. h->nelems-1] = the terms in increasing order
 *   (cf. utils/int_array_hsets)
 */
harray_t *get_term_support(support_constructor_t *constructor, term_t t) {
  term_table_t *terms;
  harray_t *result;
  int32_t i;

  terms = constructor->terms;
  i = index_of(t);
  switch (kind_for_idx(terms, i)) {
  case CONSTANT_TERM:
  case ARITH_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
    result = empty_support(constructor);
    break;

  case UNINTERPRETED_TERM:
  case VARIABLE:
    // NOTE: we use pos_term(i) here instead of t because t could be
    // of the form (not i) = neg_term(i).
    result = singleton_support(constructor, pos_term(i));
    break;

  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
  case ARITH_IS_INT_ATOM:
  case ARITH_FLOOR:
  case ARITH_CEIL:
  case ARITH_ABS:
    result = get_term_support(constructor, integer_value_for_idx(terms, i));
    break;

  case ARITH_ROOT_ATOM:
    result = lookup_support(constructor, i);
    if (result == NULL) {
      result = support_of_root_atom(constructor, root_atom_for_idx(terms, i));
      cache_support(constructor, i, result);
    }
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
    result = lookup_support(constructor, i);
    if (result == NULL) {
      result = support_of_ite(constructor, composite_for_idx(terms, i));
      cache_support(constructor, i, result);
    }
    break;

  case OR_TERM:
    result = lookup_support(constructor, i);
    if (result == NULL) {
      result = support_of_or(constructor, composite_for_idx(terms, i));
      cache_support(constructor, i, result);
    }
    break;

  case APP_TERM:
  case UPDATE_TERM:
  case TUPLE_TERM:
  case EQ_TERM:
  case DISTINCT_TERM:
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
    result = lookup_support(constructor, i);
    if (result == NULL) {
      result = support_of_composite(constructor, composite_for_idx(terms, i));
      cache_support(constructor, i, result);
    }
    break;

  case FORALL_TERM:
  case LAMBDA_TERM:
    result = lookup_support(constructor, i);
    if (result == NULL) {
      result = support_of_binding(constructor, composite_for_idx(terms, i));
      cache_support(constructor, i, result);
    }
    break;

  case SELECT_TERM:
  case BIT_TERM:
    result = get_term_support(constructor, select_for_idx(terms, i)->arg);
    break;

  case POWER_PRODUCT:
    result = lookup_support(constructor, i);
    if (result == NULL) {
      result = support_of_pprod(constructor, pprod_for_idx(terms, i));
      cache_support(constructor, i, result);
    }
    break;

  case ARITH_POLY:
    result = lookup_support(constructor, i);
    if (result == NULL) {
      result = support_of_poly(constructor, polynomial_for_idx(terms, i));
      cache_support(constructor, i, result);
    }
    break;

  case BV64_POLY:
    result = lookup_support(constructor, i);
    if (result == NULL) {
      result = support_of_bvpoly64(constructor, bvpoly64_for_idx(terms, i));
      cache_support(constructor, i, result);
    }
    break;

  case BV_POLY:
    result = lookup_support(constructor, i);
    if (result == NULL) {
      result = support_of_bvpoly(constructor, bvpoly_for_idx(terms, i));
      cache_support(constructor, i, result);
    }
    break;

  default:
    // bad term
    assert(false);
    result = NULL;
    break;
  }

  return result;
}


/*
 * Support for an array of n terms: a[0 ... n-1]
 * - every a[i] must be a valid term
 * - the support set is returned as a harray as above
 */
harray_t *get_term_array_support(support_constructor_t *constructor, const term_t *a, uint32_t n) {
  harray_t **sup;
  harray_t *result;
  uint32_t i;

  sup = (harray_t **) alloc_pstack_array(&constructor->stack, n);
  for (i=0; i<n; i++) {
    sup[i] = get_term_support(constructor, a[i]);
  }
  result = merge_harrays(&constructor->store, sup, n);
  free_pstack_array(&constructor->stack, (void **) sup);

  return result;
}

