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
 * Data structure to support term substitution
 */

#include <assert.h>

#include "terms/term_substitution.h"
#include "utils/memalloc.h"

/*
 * Check whether t is either a variable or an uninterpreted term
 * - t must be a good positive term
 */
static bool term_is_var(term_table_t *terms, term_t t) {
  assert(good_term(terms, t) && is_pos_term(t));
  switch (term_kind(terms, t)) {
  case VARIABLE:
  case UNINTERPRETED_TERM:
    return true;

  default:
    return false;
 }
}

/*
 * Check whether arrays v and t define a valid substitution:
 * - v and t must be arrays of n terms
 * - this returns true if forall i, v[i] is a variable
 *   and the type of t[i] is a subtype of v[i]'s type.
 */
bool good_term_subst(term_table_t *terms, uint32_t n, const term_t *v, const term_t *t) {
  type_table_t *types;
  uint32_t i;
  term_t x, u;

  types = terms->types;
  for (i=0; i<n; i++) {
    x = v[i];
    u = t[i];
    assert(good_term(terms, x) && good_term(terms, u));
    if (is_neg_term(x) || !term_is_var(terms, x) ||
        !is_subtype(types, term_type(terms, u), term_type(terms, x))) {
      return false;
    }
  }

  return true;
}


/*
 * Initialize subst: store the mapping v[i] --> t[i]
 */
void init_term_subst(term_subst_t *subst, term_manager_t *mngr, uint32_t n, const term_t *v, const term_t *t) {
  int_hmap_pair_t *p;
  uint32_t i;
  term_t x;

  assert(good_term_subst(term_manager_get_terms(mngr), n, v, t));

  subst->mngr = mngr;
  subst->terms = term_manager_get_terms(mngr);
  init_int_hmap(&subst->map, 0);
  init_subst_cache(&subst->cache);
  init_istack(&subst->stack);
  subst->rctx = NULL;

  for (i=0; i<n; i++) {
    x = v[i];
    assert(is_pos_term(x) && term_is_var(subst->terms, x) &&
	   good_term(subst->terms, t[i]));
    p = int_hmap_get(&subst->map, x);
    p->val = t[i];
  }
}


/*
 * Reset
 */
void reset_term_subst(term_subst_t *subst) {
  int_hmap_reset(&subst->map);
  reset_subst_cache(&subst->cache);
  reset_istack(&subst->stack);
  if (subst->rctx != NULL) {
    reset_renaming_ctx(subst->rctx);
  }
}


/*
 * Extend the current substitution:
 * - add mappings v[i] := t[i] for i=0 to n-1
 * - the new mappings must not conflict with the current subst
 * - all v[i]s must be distinct variables or uninterpreted terms
 * - the type of t[i] must be a subtype of v[i]'s type
 *
 * - if the reset flag is true, reset the cache
 */
void extend_term_subst(term_subst_t *subst, uint32_t n, const term_t *v, const term_t *t, bool reset) {
  int_hmap_pair_t *p;
  uint32_t i;
  term_t x;

  assert(good_term_subst(subst->terms, n, v, t));

  for (i=0; i<n; i++) {
    x = v[i];
    assert(is_pos_term(x) && term_is_var(subst->terms, x) &&
	   good_term(subst->terms, t[i]));
    p = int_hmap_get(&subst->map, x);
    assert(p->val < 0);
    p->val = t[i];
  }

  if (reset) {
    reset_subst_cache(&subst->cache);
  }
}


/*
 * Check whether v is in the domain of subst->map
 * - v must be a variable or uninterpreted term
 */
bool term_subst_var_in_domain(term_subst_t *subst, term_t v) {
  assert(term_is_var(subst->terms, v));
  return int_hmap_find(&subst->map, v) != NULL;
}

/*
 * Return the image of v by subst->map
 * - v must be a variable or uninterpreted term
 * - result = NULL_TERM (-1) if v is not in the map
 */
term_t term_subst_var_mapping(term_subst_t *subst, term_t v) {
  int_hmap_pair_t *p;
  term_t t;

  assert(term_is_var(subst->terms, v));

  t = NULL_TERM;
  p = int_hmap_find(&subst->map, v);
  if (p != NULL) {
    t = p->val;
    assert(good_term(subst->terms, t));
  }

  return t;
}


/*
 * Iterator for collecting variables in the substitution's domain
 * - d = vector
 */
static void add_var_to_domain(void *d, const int_hmap_pair_t *p) {
  ivector_push(d, p->key);
}


/*
 * Get the domain of the substitution
 * - every variable in subst->map is added to vector d
 */
void term_subst_domain(term_subst_t *subst, ivector_t *d) {
  ivector_reset(d);
  int_hmap_iterate(&subst->map, d, add_var_to_domain);
}


/*
 * Delete: free all memory used
 */
void delete_term_subst(term_subst_t *subst) {
  delete_int_hmap(&subst->map);
  delete_subst_cache(&subst->cache);
  delete_istack(&subst->stack);
  if (subst->rctx != NULL) {
    delete_renaming_ctx(subst->rctx);
    safe_free(subst->rctx);
    subst->rctx = NULL;
  }
}



/*
 * UTILITIES
 */

/*
 * Get the renaming context. Allocate and initialize it if needed.
 */
static renaming_ctx_t *term_subst_get_rctx(term_subst_t *subst) {
  renaming_ctx_t *tmp;

  tmp = subst->rctx;
  if (tmp == NULL) {
    tmp = (renaming_ctx_t *) safe_malloc(sizeof(renaming_ctx_t));
    init_renaming_ctx(tmp, subst->terms, 0);
    subst->rctx = tmp;
  }

  return tmp;
}

/*
 * Lookup the term mapped to x (taking renaming into account)
 * - x must be a variable
 * - if there's a renaming, lookup x in the renaming context
 * - if x is not renamed, lookup x in the map
 * - if x is not renamed and not in the map, then return x
 */
static term_t get_subst_of_var(term_subst_t *subst, term_t x) {
  int_hmap_pair_t *p;
  term_t y;

  assert(is_pos_term(x) && term_kind(subst->terms, x) == VARIABLE);

  y = NULL_TERM;
  if (subst->rctx != NULL) {
    y = renaming_ctx_lookup(subst->rctx, x);
  }
  if (y == NULL_TERM) {
    p = int_hmap_find(&subst->map, x);
    y = x;
    if (p != NULL) {
      y = p->val;
    }
  }

  return y;
}


/*
 * Lookup the term mapped to x where x is uninterpreted
 * - lookup x in the map
 * - if x is not there return x
 */
static term_t get_subst_of_unint(term_subst_t *subst, term_t x) {
  int_hmap_pair_t *p;
  term_t y;

  assert(is_pos_term(x) && term_kind(subst->terms, x) == UNINTERPRETED_TERM);

  y = x;
  p = int_hmap_find(&subst->map, x);
  if (p != NULL) {
    y = p->val;
  }

  return y;
}


/*
 * Lookup the term mapped to x where x is constant
 * - lookup x in the map
 * - if x is not there return x
 */
static term_t get_subst_of_const(term_subst_t *subst, term_t x) {
  int_hmap_pair_t *p;
  term_t y;

  assert(is_pos_term(x) && term_kind(subst->terms, x) == CONSTANT_TERM);

  y = x;
  p = int_hmap_find(&subst->map, x);
  if (p != NULL) {
    y = p->val;
  }

  return y;
}


/*
 * Check whether the result of subst(t) is stored in the cache
 * - t must be a valid term in subst->terms
 * - this takes the renaming context into account
 * - return NULL_TERM (-1) is the result is not in the cache
 */
static term_t get_cached_subst(term_subst_t *subst, term_t t) {
  renaming_ctx_t *ctx;
  harray_t *hashed_ctx;

  assert(is_pos_term(t) && good_term(subst->terms, t));

  hashed_ctx = NULL;
  ctx = subst->rctx;
  if (ctx != NULL && !renaming_ctx_is_empty(ctx)) {
    hashed_ctx = renaming_ctx_hash(ctx);
  }

  return subst_cache_lookup(&subst->cache, hashed_ctx, t);
}


/*
 * Add u as subst(t) in the cache
 * - t and u must be valid terms in subst->terms
 * - there must not be an existing value for t in the cache
 * - this takes the renaming context into account (cf. subst_cache.h)
 */
static void cache_subst_result(term_subst_t *subst, term_t t, term_t u) {
  renaming_ctx_t *ctx;
  harray_t *hashed_ctx;

  assert(is_pos_term(t) && good_term(subst->terms, t) && good_term(subst->terms, u));

  hashed_ctx = NULL;
  ctx = subst->rctx;
  if (ctx != NULL && !renaming_ctx_is_empty(ctx)) {
    hashed_ctx = renaming_ctx_hash(ctx);
  }

  subst_cache_add(&subst->cache, hashed_ctx, t, u);
}


/*
 * Extend the current renaming context: by renaming for v[0 .. n-1]
 * (cf. renaming_context.h)
 * - v[0] ... v[n-1] must all be variables in subst->terms
 * - this allocates and initializes the renaming data structure if needed
 */
static void subst_push_renaming(term_subst_t *subst, uint32_t n, term_t *v) {
  renaming_ctx_t *ctx;

  ctx = term_subst_get_rctx(subst);
  renaming_ctx_push_vars(ctx, n, v);
}


/*
 * Remove the last n variable renaming (cf. renaming_context.h)
 * - the current renaming must exist and have at least n variables
 */
static void subst_pop_renaming(term_subst_t *subst, uint32_t n) {
  assert(subst->rctx != NULL);
  renaming_ctx_pop_vars(subst->rctx, n);
}




/*
 * POWER PRODUCTS
 */

/*
 * Check whether the product a[0]^e_0 ... a[n-1]^e_{n-1} has degree > YICES_MAX_DEGREE
 * - e_i = exponent in pprod p
 */
static bool pprod_degree_overflows(term_table_t *tbl, pprod_t *p, uint32_t n, term_t *a) {
  uint64_t d;
  uint32_t i;

  assert(n == p->len);

  d = 0;
  for (i=0; i<n; i++) {
    d += ((uint64_t) term_degree(tbl, a[i])) * p->prod[i].exp;
    if (d > (uint64_t) YICES_MAX_DEGREE) {
      return true;
    }
  }

  return false;
}


/*
 * Check whether term t is 0
 * - t is either an arithmetic or a bitvector term
 */
static bool term_is_zero(term_table_t *tbl, term_t t) {
  bvconst_term_t *c;
  uint32_t k;

  assert(is_arithmetic_term(tbl, t) || is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case ARITH_CONSTANT:
    assert(t == zero_term || q_is_nonzero(rational_term_desc(tbl, t)));;
    return t == zero_term;

  case BV64_CONSTANT:
    return bvconst64_term_desc(tbl, t)->value == (uint64_t) 0;

  case BV_CONSTANT:
    c = bvconst_term_desc(tbl, t);
    k = (c->bitsize + 31) >> 5;
    return bvconst_is_zero(c->data, k);

  default:
    return false;
  }
}



/*
 * BETA-REDUCTION/RECURSIVE SUBSTITUTION
 */

#define TRACE 0

#if TRACE

#include "io/term_printer.h"

static void trace_beta_reduction(term_table_t *tbl, term_t t, term_t u) {
  pp_area_t area;

  area.width = 80;
  area.height = 20;
  area.offset = 8;
  area.stretch = false;
  area.truncate = true;

  printf("--- Beta reduction ---\n");
  printf("input:  ");
  pretty_print_term_exp(stdout, &area, tbl, t);
  printf("output: ");
  pretty_print_term_full(stdout, &area, tbl, u);
  printf("--\n");
}

#endif

/*
 * Apply a (lambda (x_0 ... x_n-1) t) to arguments arg[0 ... n-1]
 * - lambda is the term_descriptor of (lambda (x_0 ... x_n) t)
 * - arg = array of n terms
 */
static term_t apply_beta_rule(term_manager_t *mngr, composite_term_t *lambda, term_t *arg) {
  term_subst_t subst;
  uint32_t n;
  term_t u;

  assert(lambda->arity >= 2);
  n = lambda->arity - 1; // number of variables
  init_term_subst(&subst, mngr, n, lambda->arg, arg);
  u = apply_term_subst(&subst, lambda->arg[n]);
  delete_term_subst(&subst);

  return u;
}


/*
 * Apply beta-reduction to t
 * - if t is not of the from (apply (lambda (x_1 ... x_n) u) t_1 ... t_n) then
 *   it's returned unchanged
 * - otherwise, apply the substitution [x_1 := t_1, ... x_n := t_n] to u and return
 *   the result
 *
 * Possible error codes are the same as in apply_term_subst:
 * - return -1 (NULL_TERM) if the substitution causes a degree overflow
 * - return -2 if an exception is raised (bug somewhere)
 */
term_t beta_reduce(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;
  composite_term_t *app;
  term_t f, u;

  u = t;
  tbl = term_manager_get_terms(mngr);
  if (term_kind(tbl, t) == APP_TERM) {
    app = app_term_desc(tbl, t);
    f = app->arg[0];
    if (term_kind(tbl, f) == LAMBDA_TERM) {
      u = apply_beta_rule(mngr, lambda_term_desc(tbl, f), app->arg + 1);

#if TRACE
      trace_beta_reduction(tbl, t, u);
#endif
    }
  }

  return u;
}



/*
 * APPLY SUBSTITUTION
 */

/*
 * Main recursive function
 * - apply 'subst' to 't': return the result
 *
 * Error codes returned:
 * - if the substitution creates a term of degree > YICES_MAX_DEGREE
 *   abort by calling longjmp(subst->env): return -1 (NULL_TERM)
 * - if something else goes wrong (either because the substitution is wrong
 *   or there's a bug somewhere): return -2
 */
static term_t get_subst(term_subst_t *subst, term_t t);


/*
 * Apply substitution to 'FORALL x1 ... x_n: b'
 * - d has arity n+1 >= 2
 * - d->arg[0] ... d->arg[n-1] = variables x_1 ... x_n
 * - d->arg[n] = body b
 */
static term_t subst_forall(term_subst_t *subst, composite_term_t *d) {
  term_t result;
  int32_t *a;
  uint32_t n;

  assert(d->arity >= 2);

  n = d->arity - 1;

  // add renaming for variables x1 ... x_n to x'1 ... x'n
  subst_push_renaming(subst, n, d->arg);
  assert(subst->rctx != NULL);

  // store the new variables x'1 ... x'k in array a
  a = alloc_istack_array(&subst->stack, n);
  renaming_ctx_collect_new_vars(subst->rctx, n, a);

  // build (FORALL x'1 ... x'k: subst(body))
  result = get_subst(subst, d->arg[n]);
  result = mk_forall(subst->mngr, n, a, result);

  // cleanup
  free_istack_array(&subst->stack, a);
  subst_pop_renaming(subst, n);

  return result;
}


/*
 * Apply substitution to 'LAMBDA x1 ... x_n : b'
 * - d has arity n+1 >= 2
 * - d->arg[0] ... d->arg[n-1] = variables
 * - d->arg[n] = body
 */
static term_t subst_lambda(term_subst_t *subst, composite_term_t *d) {
  term_t result;
  int32_t *a;
  uint32_t n;

  assert(d->arity >= 2);

  n = d->arity - 1;

  // add renaming for variables x1 ... x_n to x'1 ... x'n
  subst_push_renaming(subst, n, d->arg);
  assert(subst->rctx != NULL);

  // store the new variables x'1 ... x'k in array a
  a = alloc_istack_array(&subst->stack, n);
  renaming_ctx_collect_new_vars(subst->rctx, n, a);

  // build (LAMBDA x'1 ... x'k: subst(body))
  result = get_subst(subst, d->arg[n]);
  result = mk_lambda(subst->mngr, n, a, result);

  // cleanup
  free_istack_array(&subst->stack, a);
  subst_pop_renaming(subst, n);

  return result;
}




/*
 * Auxiliary function: apply subst recursively to all children of d
 * - return the result in array a, allocated in the subst->stack
 */
static term_t *subst_children(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  uint32_t i, n;

  n = d->arity;
  a = alloc_istack_array(&subst->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_subst(subst, d->arg[i]);
  }

  return a;
}


/*
 * Substitution for all other composite terms
 */

// t = 0
static term_t subst_arith_eq(term_subst_t *subst, term_t t) {
  term_t u;

  u = get_subst(subst, t);
  return mk_arith_term_eq0(subst->mngr, u);
}

// t >= 0
static term_t subst_arith_ge(term_subst_t *subst, term_t t) {
  term_t u;

  u = get_subst(subst, t);
  return mk_arith_term_geq0(subst->mngr, u);
}

// (is-int t)
static term_t subst_arith_is_int(term_subst_t *subst, term_t t) {
  term_t u;

  u = get_subst(subst, t);
  return mk_arith_is_int(subst->mngr, u);
}

// (floor t)
static term_t subst_arith_floor(term_subst_t *subst, term_t t) {
  term_t u;

  u = get_subst(subst, t);
  return mk_arith_floor(subst->mngr, u);
}

// (ceil t)
static term_t subst_arith_ceil(term_subst_t *subst, term_t t) {
  term_t u;

  u = get_subst(subst, t);
  return mk_arith_ceil(subst->mngr, u);
}

// (abs t)
static term_t subst_arith_abs(term_subst_t *subst, term_t t) {
  term_t u;

  u = get_subst(subst, t);
  return mk_arith_abs(subst->mngr, u);
}

// (ite c t1 t2)
static term_t subst_ite(term_subst_t *subst, composite_term_t *d) {
  term_table_t *tbl;
  term_t c, t1, t2;
  type_t tau;
  term_t result;

  assert(d->arity == 3);

  c = get_subst(subst, d->arg[0]); // condition
  if (c == true_term) {
    result = get_subst(subst, d->arg[1]);
  } else if (c == false_term) {
    result = get_subst(subst, d->arg[2]);
  } else {
    t1 = get_subst(subst, d->arg[1]);
    t2 = get_subst(subst, d->arg[2]);

    tbl = subst->terms;
    tau = super_type(tbl->types, term_type(tbl, t1), term_type(tbl, t2));
    assert(tau != NULL_TYPE);

    result = mk_ite(subst->mngr, c, t1, t2, tau);
  }

  return result;
}

// function application
static term_t subst_app(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  term_t result;

  assert(d->arity >= 2);

  // a[0] = function, a[1 ... n-1] = arguments
  a = subst_children(subst, d);
  result = mk_application(subst->mngr, a[0], d->arity-1, a+1);
  free_istack_array(&subst->stack, a);

  // a[0] may be a lambda term so we check for beta-reduction here
  return beta_reduce(subst->mngr, result);
}

// function update
static term_t subst_update(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  term_t result;
  uint32_t n;

  assert(d->arity >= 3);

  // a[0] = function, a[1..n-2] = argument, a[n-1] = new_v
  a = subst_children(subst, d);
  n = d->arity;
  result = mk_update(subst->mngr, a[0], n-2, a+1, a[n-1]);
  free_istack_array(&subst->stack, a);

  return result;
}

// tuple
static term_t subst_tuple(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  term_t result;

  a = subst_children(subst, d);
  result = mk_tuple(subst->mngr, d->arity, a);
  free_istack_array(&subst->stack, a);

  return result;
}

// equality
static term_t subst_eq(term_subst_t *subst, composite_term_t *d) {
  term_t t, u;

  assert(d->arity == 2);
  t = get_subst(subst, d->arg[0]);
  u = get_subst(subst, d->arg[1]);
  return mk_eq(subst->mngr, t, u);
}

// distinct
static term_t subst_distinct(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  term_t result;

  a = subst_children(subst, d);
  result = mk_distinct(subst->mngr, d->arity, a);
  free_istack_array(&subst->stack, a);

  return result;
}

// or
static term_t subst_or(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  term_t result;
  uint32_t i, n;

  n = d->arity;
  assert(n >= 2);

  a = alloc_istack_array(&subst->stack, n);
  result = true_term;
  for (i=0; i<n; i++) {
    a[i] = get_subst(subst, d->arg[i]);
    if (a[i] == true_term) goto done; // result is true_term
  }

  // no simplification:
  result = mk_or(subst->mngr, n, a);

 done:
  free_istack_array(&subst->stack, a);

  return result;
}

// xor
static term_t subst_xor(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  term_t result;

  assert(d->arity >= 2);
  a = subst_children(subst, d);
  result = mk_xor(subst->mngr, d->arity, a);
  free_istack_array(&subst->stack, a);

  return result;
}

// (eq t1 t2): arithmetic
static term_t subst_arith_bineq(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_arith_eq(subst->mngr, t1, t2);
}

// (/ t1 t2)
static term_t subst_arith_rdiv(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_arith_rdiv(subst->mngr, t1, t2);
}

// (div t1 t2)
static term_t subst_arith_idiv(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_arith_idiv(subst->mngr, t1, t2);
}

// (mod t1 t2)
static term_t subst_arith_mod(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_arith_mod(subst->mngr, t1, t2);
}

// (divides t1 t2)
static term_t subst_arith_divides(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_arith_divides(subst->mngr, t1, t2);
}

// array of bits
static term_t subst_bvarray(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  term_t result;

  assert(d->arity >= 1);
  a = subst_children(subst, d);
  result = mk_bvarray(subst->mngr, d->arity, a);
  free_istack_array(&subst->stack, a);

  return result;
}

// bitvector division and shift operators
static term_t subst_bvdiv(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvdiv(subst->mngr, t1, t2);
}

static term_t subst_bvrem(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvrem(subst->mngr, t1, t2);
}

static term_t subst_bvsdiv(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvsdiv(subst->mngr, t1, t2);
}

static term_t subst_bvsrem(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvsrem(subst->mngr, t1, t2);
}

static term_t subst_bvsmod(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvsmod(subst->mngr, t1, t2);
}

static term_t subst_bvshl(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvshl(subst->mngr, t1, t2);
}

static term_t subst_bvlshr(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvlshr(subst->mngr, t1, t2);
}

static term_t subst_bvashr(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvashr(subst->mngr, t1, t2);
}

// bitvector atoms
static term_t subst_bveq(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bveq(subst->mngr, t1, t2);
}

static term_t subst_bvge(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvge(subst->mngr, t1, t2);
}

static term_t subst_bvsge(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvsge(subst->mngr, t1, t2);
}

/*
 * projection and bit select
 *
 * Warning: d is not a safe pointer (it may become invalid if new
 * terms are created). cf. terms.h
 *
 * So we must make a copy of d->idx before the recursive call
 */
static term_t subst_select(term_subst_t *subst, select_term_t *d) {
  uint32_t idx;
  term_t t;

  idx = d->idx;
  t = get_subst(subst, d->arg);
  return mk_select(subst->mngr, idx, t);
}

static term_t subst_bit_select(term_subst_t *subst, select_term_t *d) {
  uint32_t idx;
  term_t t;

  idx = d->idx;
  t = get_subst(subst, d->arg);
  return mk_bitextract(subst->mngr, t, idx);
}


/*
 * Power products
 */
static term_t subst_pprod(term_subst_t *subst, pprod_t *p, type_t tau) {
  term_t *a;
  term_t result;
  uint32_t i, n, nbits;

  n = p->len;
  a = alloc_istack_array(&subst->stack, n);

  /*
   * p is t_0^e_0 ... t_{n-1}^e_{n-1}
   * compute a[i] = subst(t_i), stop if a[i] is zero
   */
  for (i=0; i<n; i++) {
    a[i] = get_subst(subst, p->prod[i].var);
    if (term_is_zero(subst->terms, a[i])) {
      // the result is zero
      result = a[i];
      goto done;
    }
  }

  /*
   * Check for overflow
   */
  if (pprod_degree_overflows(subst->terms, p, n, a)) {
    longjmp(subst->env, -1); // raise an exception
  }

  /*
   * build the term a[0] ^ e_0 ... a[n-1]^ e_{n-1}
   */
  if (is_arithmetic_type(tau)) {
    result = mk_arith_pprod(subst->mngr, p, n, a);
  } else {
    nbits = bv_type_size(subst->terms->types, tau);
    if (nbits <= 64) {
      result =  mk_bvarith64_pprod(subst->mngr, p, n, a, nbits);
    } else {
      result = mk_bvarith_pprod(subst->mngr, p, n, a, nbits);
    }
  }

 done:
  free_istack_array(&subst->stack, a);

  return result;
}


/*
 * Arithmetic polynomial
 */
static term_t subst_poly(term_subst_t *subst, polynomial_t *p) {
  term_t *a;
  term_t result;
  uint32_t i, n;

  n = p->nterms;
  a = alloc_istack_array(&subst->stack, n);

  // skip the constant term if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[i] = const_idx;
    i ++;
  }

  // rest of the terms in p
  while (i < n) {
    a[i] = get_subst(subst, p->mono[i].var);
    i ++;
  }

  // build the polynomial
  result = mk_arith_poly(subst->mngr, p, n, a);

  free_istack_array(&subst->stack, a);

  return result;
}


/*
 * Bitvector polynomial: 64bit coefficients
 */
static term_t subst_bvpoly64(term_subst_t *subst, bvpoly64_t *p) {
  term_t *a;
  term_t result;
  uint32_t i, n;

  n = p->nterms;
  a = alloc_istack_array(&subst->stack, n);

  // skip the constant term if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[i] = const_idx;
    i ++;
  }

  // rest of the terms in p
  while (i < n) {
    a[i] = get_subst(subst, p->mono[i].var);
    i ++;
  }

  // build the polynomial
  result = mk_bvarith64_poly(subst->mngr, p, n, a);

  free_istack_array(&subst->stack, a);

  return result;
}


/*
 * Bitvector polynomial: more than 64bits
 */
static term_t subst_bvpoly(term_subst_t *subst, bvpoly_t *p) {
  term_t *a;
  term_t result;
  uint32_t i, n;

  n = p->nterms;
  a = alloc_istack_array(&subst->stack, n);

  // skip the constant term if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[i] = const_idx;
    i ++;
  }

  // rest of the terms in p
  while (i < n) {
    a[i] = get_subst(subst, p->mono[i].var);
    i ++;
  }

  // build the polynomial
  result = mk_bvarith_poly(subst->mngr, p, n, a);

  free_istack_array(&subst->stack, a);

  return result;
}



/*
 * Core function: recursively compute subst for a composite term t
 * - t has positive polarity
 * - t is a valid term in the term table
 * - t is a composite term
 */
static term_t subst_composite(term_subst_t *subst, term_t t) {
  term_table_t *terms;
  term_t result;

  terms = subst->terms;
  assert(good_term(terms, t) && is_pos_term(t));

  switch (term_kind(terms, t)) {
  case ARITH_EQ_ATOM:
    result = subst_arith_eq(subst, arith_eq_arg(terms, t));
    break;

  case ARITH_GE_ATOM:
    result = subst_arith_ge(subst, arith_ge_arg(terms, t));
    break;

  case ARITH_ROOT_ATOM:
    // TODO
    assert(false);
    result = NULL_TERM;
    break;

  case ARITH_IS_INT_ATOM:
    result = subst_arith_is_int(subst, arith_is_int_arg(terms, t));
    break;

  case ARITH_FLOOR:
    result = subst_arith_floor(subst, arith_floor_arg(terms, t));
    break;

  case ARITH_CEIL:
    result = subst_arith_ceil(subst, arith_ceil_arg(terms, t));
    break;

  case ARITH_ABS:
    result = subst_arith_abs(subst, arith_abs_arg(terms, t));
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
    result = subst_ite(subst, ite_term_desc(terms, t));
    break;

  case APP_TERM:
    result = subst_app(subst, app_term_desc(terms, t));
    break;

  case UPDATE_TERM:
    result = subst_update(subst, update_term_desc(terms, t));
    break;

  case TUPLE_TERM:
    result = subst_tuple(subst, tuple_term_desc(terms, t));
    break;

  case EQ_TERM:
    result = subst_eq(subst, eq_term_desc(terms, t));
    break;

  case DISTINCT_TERM:
    result = subst_distinct(subst, distinct_term_desc(terms, t));
    break;

  case FORALL_TERM:
    result = subst_forall(subst, forall_term_desc(terms, t));
    break;

  case LAMBDA_TERM:
    result = subst_lambda(subst, lambda_term_desc(terms, t));
    break;

  case OR_TERM:
    result = subst_or(subst, or_term_desc(terms, t));
    break;

  case XOR_TERM:
    result = subst_xor(subst, xor_term_desc(terms, t));
    break;

  case ARITH_BINEQ_ATOM:
    result = subst_arith_bineq(subst, arith_bineq_atom_desc(terms, t));
    break;

  case ARITH_RDIV:
    result = subst_arith_rdiv(subst, arith_rdiv_term_desc(terms, t));
    break;
 
  case ARITH_IDIV:
    result = subst_arith_idiv(subst, arith_idiv_term_desc(terms, t));
    break;

 case ARITH_MOD:
    result = subst_arith_mod(subst, arith_mod_term_desc(terms, t));
    break;

  case ARITH_DIVIDES_ATOM:
    result = subst_arith_divides(subst, arith_divides_atom_desc(terms, t));
    break;

  case BV_ARRAY:
    result = subst_bvarray(subst, bvarray_term_desc(terms, t));
    break;

  case BV_DIV:
    result = subst_bvdiv(subst, bvdiv_term_desc(terms, t));
    break;

  case BV_REM:
    result = subst_bvrem(subst, bvrem_term_desc(terms, t));
    break;

  case BV_SDIV:
    result = subst_bvsdiv(subst, bvsdiv_term_desc(terms, t));
    break;

  case BV_SREM:
    result = subst_bvsrem(subst, bvsrem_term_desc(terms, t));
    break;

  case BV_SMOD:
    result = subst_bvsmod(subst, bvsmod_term_desc(terms, t));
    break;

  case BV_SHL:
    result = subst_bvshl(subst, bvshl_term_desc(terms, t));
    break;

  case BV_LSHR:
    result = subst_bvlshr(subst, bvlshr_term_desc(terms, t));
    break;

  case BV_ASHR:
    result = subst_bvashr(subst, bvashr_term_desc(terms, t));
    break;

  case BV_EQ_ATOM:
    result = subst_bveq(subst, bveq_atom_desc(terms, t));
    break;

  case BV_GE_ATOM:
    result = subst_bvge(subst, bvge_atom_desc(terms, t));
    break;

  case BV_SGE_ATOM:
    result = subst_bvsge(subst, bvsge_atom_desc(terms, t));
    break;

  case SELECT_TERM:
    result = subst_select(subst, select_term_desc(terms, t));
    break;

  case BIT_TERM:
    result = subst_bit_select(subst, bit_term_desc(terms, t));
    break;

  case POWER_PRODUCT:
    result = subst_pprod(subst, pprod_term_desc(terms, t), term_type(terms, t));
    break;

  case ARITH_POLY:
    result = subst_poly(subst, poly_term_desc(terms, t));
    break;

  case BV64_POLY:
    result = subst_bvpoly64(subst, bvpoly64_term_desc(terms, t));
    break;

  case BV_POLY:
    result = subst_bvpoly(subst, bvpoly_term_desc(terms, t));
    break;

  default:
    // error: invalid term_kind or not a composite
    longjmp(subst->env, -2);
    break;
  }

  return result;
}


/*
 * Main substitution function:
 * - if t is atomic and constant return t
 * - if t is a variable, lookup what's mapped to t in subst
 * - otherwise t is composite:
 *   if t is ground, return t
 *   if t is not ground, check the cache; if subst(t) is not
 *   in the cache recursively compute it and store that in the cache.
 */
static term_t get_subst(term_subst_t *subst, term_t t) {
  term_table_t *terms;
  uint32_t polarity;
  term_t result;

  terms = subst->terms;
  assert(good_term(terms, t));

  polarity = polarity_of(t);
  t = unsigned_term(t);

  switch (term_kind(terms, t)) {
  case ARITH_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
    result = t;
    break;

  case VARIABLE:
    result = get_subst_of_var(subst, t);
    break;

  case UNINTERPRETED_TERM:
    result = get_subst_of_unint(subst, t);
    break;

  case CONSTANT_TERM:
    result = get_subst_of_const(subst, t);
    break;

  default:
    /*
     * Composite term
     */
    result = get_cached_subst(subst, t);
    if (result < 0) {
      assert(result == NULL_TERM);
      result = subst_composite(subst, t);
      cache_subst_result(subst, t, result);
    }
    break;
  }

  assert(good_term(terms, result));

  return result ^ polarity;
}



/*
 * Apply the substitution to term t
 * - t must be a valid term in the subst's term manager
 * - return the resulting term
 *
 * Error codes:
 * - return -1 if the result can't be constructed
 *   (because of a degree overflow).
 * - return -2 if something else goes wrong
 */
term_t apply_term_subst(term_subst_t *subst, term_t t) {
  term_t result;
  int code;

  code = setjmp(subst->env);
  if (code == 0) {
    result = get_subst(subst, t);
  } else {
    // Error code
    assert(code == -1 || code == -2);
    result = (term_t) code;

    // Cleanup
    reset_istack(&subst->stack);
    if (subst->rctx != NULL) {
      reset_renaming_ctx(subst->rctx);
    }
  }

  return result;
}



