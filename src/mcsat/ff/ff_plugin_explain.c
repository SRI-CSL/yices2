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

#include <poly/poly.h>
#include <poly/polynomial.h>
#include <poly/polynomial_heap.h>
#include <poly/polynomial_hash_set.h>

#include "mcsat/ff/ff_plugin_explain.h"
#include "mcsat/ff/ff_plugin_internal.h"

#include "mcsat/tracing.h"

static
void explain_single(const lp_data_t *lp_data, const lp_polynomial_t *A, lp_polynomial_hash_set_t *e_ne);

/** finalizes and empties eq and ne (to avoid polynomial copying) */
static
void explain_multi(const lp_data_t *lp_data,
                   lp_polynomial_hash_set_t *eq, lp_polynomial_hash_set_t *ne,
                   lp_polynomial_hash_set_t *e_eq, lp_polynomial_hash_set_t *e_ne);

#ifndef NDEBUG
static
bool check_assignment_poly(const lp_polynomial_t *p, const lp_assignment_t *m) {
  assert(lp_polynomial_is_assigned(p, m));
  lp_integer_t val;
  lp_integer_construct(&val);
  lp_polynomial_evaluate_integer(p, m, &val);
  bool is_zero = lp_integer_is_zero(lp_polynomial_get_context(p)->K, &val);
  lp_integer_destruct(&val);
  return is_zero;
}

static
bool check_hash_set_all(const lp_polynomial_hash_set_t *v, const lp_assignment_t *m, bool negated) {
  assert(v->closed);
  for (int i = 0; i < v->size; ++i) {
    bool is_zero = check_assignment_poly(v->data[i], m);
    if (!is_zero == !negated) {
      return false;
    }
  }
  return true;
}

static
bool check_assignment_cube(const lp_polynomial_hash_set_t *eq, const lp_polynomial_hash_set_t *ne, const lp_assignment_t *m) {
  if (eq && !check_hash_set_all(eq, m, false)) {
    return false;
  }
  if (ne && !check_hash_set_all(ne, m, true)) {
    return false;
  }
  return true;
}
#endif

static
void exclude_coefficient(const lp_polynomial_t *A, const lp_assignment_t *m, lp_variable_t var, lp_polynomial_hash_set_t *result) {
  const lp_polynomial_context_t *ctx = lp_polynomial_get_context(A);

  if (lp_polynomial_is_constant(A))
    return;

  lp_polynomial_t *tmp;
  lp_monomial_t mon;
  lp_monomial_construct(ctx, &mon);
  lp_integer_t num;
  lp_integer_construct(&num);

  if (lp_polynomial_top_variable(A) != var) {
    assert(lp_polynomial_is_assigned(A, m));
    tmp = lp_polynomial_new_copy(A);
    lp_polynomial_evaluate_integer(A, m, &num);
    lp_integer_neg(ctx->K, &num, &num);
    lp_monomial_set_coefficient(ctx, &mon, &num);
    lp_polynomial_add_monomial(tmp, &mon);
    lp_polynomial_hash_set_insert(result, tmp);
  } else {
    const size_t degree = lp_polynomial_degree(A);
    tmp = lp_polynomial_new(ctx);
    for (size_t k = 0; k <= degree; ++k) {
      lp_polynomial_get_coefficient(tmp, A, k);
      if (lp_polynomial_is_constant(tmp))
        continue;
      lp_polynomial_evaluate_integer(tmp, m, &num);
      lp_integer_neg(ctx->K, &num, &num);
      lp_monomial_set_coefficient(ctx, &mon, &num);
      lp_polynomial_add_monomial(tmp, &mon);
      lp_polynomial_hash_set_insert(result, tmp);
    }
  }
  lp_polynomial_delete(tmp);
  lp_integer_destruct(&num);
  lp_monomial_destruct(&mon);
}

static
void explain_single(const lp_data_t *lp_data, const lp_polynomial_t *A, lp_polynomial_hash_set_t *e_ne) {
  const lp_assignment_t *m = lp_data->lp_assignment;

  assert(lp_polynomial_is_univariate_m(A, m));

  // maybe make internal copy to avoid repeated checks for order at get_coefficient
  // lp_polynomial_construct_copy
  // lp_polynomial_ensure_order
  // or maybe do this in polynomial_coefficient_traverse and use it here

  if (ctx_trace_enabled(lp_data->plugin_ctx, "ff::explain")) {
    ctx_trace_printf(lp_data->plugin_ctx, "explain_single ( ");
    lp_polynomial_print(A, ctx_trace_out(lp_data->plugin_ctx));
    ctx_trace_printf(lp_data->plugin_ctx, ", ");
    lp_assignment_print(m, ctx_trace_out(lp_data->plugin_ctx));
    ctx_trace_printf(lp_data->plugin_ctx, ")\n");
  }

  lp_variable_t top = lp_polynomial_top_variable(A);
  assert(!lp_assignment_is_set(m, top));
  assert(lp_polynomial_is_univariate_m(A, m));
  exclude_coefficient(A, m, top, e_ne);
  lp_polynomial_hash_set_close(e_ne);

  if (ctx_trace_enabled(lp_data->plugin_ctx, "ff::explain")) {
    ctx_trace_printf(lp_data->plugin_ctx, "explain_single () => ");
    lp_polynomial_hash_set_print(e_ne, stdout);
    ctx_trace_printf(lp_data->plugin_ctx, "\n");
  }
}

static inline
int heap_contains_check_top_variable(const lp_polynomial_heap_t *heap, lp_variable_t top) {
  for (size_t i = 0; i < lp_polynomial_heap_size(heap); ++i) {
    if (lp_polynomial_top_variable(lp_polynomial_heap_at(heap, i)) != top) {
      return 0;
    }
  }
  return 1;
}

static inline
size_t polynomial_degree_safe(const lp_polynomial_t *A, lp_variable_t v) {
  return lp_polynomial_top_variable(A) == v ? lp_polynomial_degree(A) : 0;
}

static
lp_polynomial_t** srs(const lp_polynomial_t *f, const lp_polynomial_t *g, size_t *count) {
  assert(lp_polynomial_context_equal(lp_polynomial_get_context(f), lp_polynomial_get_context(g)));
  assert(lp_polynomial_top_variable(f) == lp_polynomial_top_variable(g));

  const lp_polynomial_context_t *ctx = lp_polynomial_get_context(f);
  const lp_variable_t var = lp_polynomial_top_variable(f);
  // calculate size of subres
  size_t
      deg_f = lp_polynomial_degree(f),
      deg_g = lp_polynomial_degree(g);

  size_t cnt = (deg_f < deg_g ? deg_f : deg_g) + 1;

  // prepare memory
  lp_polynomial_t
      **subres = safe_malloc(sizeof(lp_polynomial_t*) * (cnt+1)),
      **srs = safe_malloc(sizeof(lp_polynomial_t*) * (cnt+1));

  for (size_t i = 0; i < cnt; ++i) {
    subres[i] = lp_polynomial_new(ctx);
  }

  // generate subresultants
  lp_polynomial_srs(subres, f, g);

  // remove defective
  *count = 0;
  for (int i = 0; i < cnt; ++i) {
    if (polynomial_degree_safe(subres[i], var) == i) {
      srs[*count] = subres[i];
      (*count) ++;
    } else {
      lp_polynomial_delete(subres[i]);
    }
  }
  free(subres);

  // return sub-chain
  return srs;
}

/** Gets (a new instance of) the lc(p). Assumes that top(p) <= var. */
static
lp_polynomial_t* lc(const lp_polynomial_t *p, lp_variable_t var) {
  const lp_polynomial_context_t *ctx = lp_polynomial_get_context(p);
  size_t d = polynomial_degree_safe(p, var);
  if (d == 0) {
    return lp_polynomial_new_copy(p);
  }
  lp_polynomial_t *lc = lp_polynomial_new(ctx);
  lp_polynomial_get_coefficient(lc, p, d);
  return lc;
}

static inline
int polynomial_is_zero_m(const lp_polynomial_t *A, const lp_assignment_t *m) {
  assert(lp_polynomial_is_assigned(A, m));

  lp_integer_t val;
  lp_integer_construct(&val);
  lp_polynomial_evaluate_integer(A, m, &val);
  int ret = lp_integer_is_zero(lp_polynomial_get_context(A)->K, &val);
  lp_integer_destruct(&val);
  return ret;
}

static inline
int polynomial_is_assigned_and_zero(const lp_polynomial_t *p, const lp_assignment_t *m) {
  return lp_polynomial_is_assigned(p, m) && polynomial_is_zero_m(p, m);
}

static inline
int polynomial_is_assigned_and_non_zero(const lp_polynomial_t *p, const lp_assignment_t *m) {
  return lp_polynomial_is_assigned(p, m) && !polynomial_is_zero_m(p, m);
}

static inline
int polynomial_lc_is_assigned_and_non_zero(const lp_polynomial_t *p, lp_variable_t var, const lp_assignment_t *m) {
  lp_polynomial_t *p_lc = lc(p, var);
  int rslt = polynomial_is_assigned_and_non_zero(p_lc, m);
  lp_polynomial_delete(p_lc);
  return rslt;
}

static inline
lp_polynomial_t* red(const lp_polynomial_t *p, lp_variable_t var) {
  assert(lp_polynomial_top_variable(p) == var);
  (void)var;
  const lp_polynomial_context_t *ctx = lp_polynomial_get_context(p);
  lp_polynomial_t *red = lp_polynomial_new(ctx);
  lp_polynomial_reductum(red, p);
  return red;
}

static inline
lp_polynomial_t* pquo(const lp_polynomial_t *A, const lp_polynomial_t *B, lp_variable_t var) {
  assert(lp_polynomial_top_variable(A) == var);
  const lp_polynomial_context_t *ctx = lp_polynomial_get_context(A);
  lp_polynomial_t *quo = lp_polynomial_new(ctx);
  lp_polynomial_t *rem = lp_polynomial_new(ctx);
  lp_polynomial_pdivrem(quo, rem, A, B);
  lp_polynomial_delete(rem);
  return quo;
}

/** Checks the lc of p wrt. to var, checks if the variable is neq_zero and adds it to the correct side-condition set (M or N) */
static inline
int track_lc_branch_condition(const lp_polynomial_t *p, const lp_assignment_t *m, lp_variable_t var, int neq_zero,
                              lp_polynomial_hash_set_t *M, lp_polynomial_hash_set_t *N) {
  lp_polynomial_t *p_lc = lc(p, var);
  assert(lp_polynomial_is_assigned(p_lc, m));
  int is_zero = polynomial_is_zero_m(p_lc, m);
  if (!lp_polynomial_is_constant(p_lc)) {
    lp_polynomial_hash_set_insert_move(is_zero ? M : N, p_lc);
  }
  lp_polynomial_delete(p_lc);
  // is_zero xor neq_zero
  return !is_zero != !neq_zero;
}

typedef enum {
  /* no processing possible */
  NOT_APPLICABLE = 0,
  /* excluding polynomial was found */
  FOUND,
  /* degree reduction performed, but no excluding polynomial was found */
  PROCESSED
} explain_result_t;

static
explain_result_t explain_p(const lp_polynomial_t *p2,
                           lp_polynomial_heap_t *F, lp_polynomial_heap_t *G,
                           lp_polynomial_hash_set_t *M, lp_polynomial_hash_set_t *N,
                           const lp_assignment_t *m, lp_variable_t var) {

  explain_result_t rslt = NOT_APPLICABLE;
  if (track_lc_branch_condition(p2, m, var, 0, M, N)) {
    lp_polynomial_t *red_p2 = red(p2, var);
    if (polynomial_is_assigned_and_non_zero(red_p2, m)) {
      lp_polynomial_hash_set_insert(N, red_p2);
      rslt = FOUND;
    } else {
      if (lp_polynomial_top_variable(red_p2) == var) { lp_polynomial_heap_push(F, red_p2); }
      rslt = PROCESSED;
    }
    lp_polynomial_delete(red_p2);
  }
  return rslt;
}

/** tries to reduce F wrt. to p2 by finding a gcd with one element from F */
static
explain_result_t explain_pP(const lp_polynomial_t *p2,
                            lp_polynomial_heap_t *F, lp_polynomial_heap_t *G,
                            lp_polynomial_hash_set_t *M, lp_polynomial_hash_set_t *N,
                            const lp_assignment_t *m, lp_variable_t var) {

  lp_polynomial_t *p1 = lp_polynomial_heap_pop(F);

  size_t r;
  lp_polynomial_t **h = srs(p1, p2, &r);

  explain_result_t ret = NOT_APPLICABLE;
  size_t i = 0;
  if (lp_polynomial_top_variable(h[0]) != var) {
    assert(r >= 1);
    i++;
    // since h[0] has no var, it is in F for all potential branches.
    // If it is excluding, all branches are excluded,...
    assert(lp_polynomial_is_assigned(h[0], m));
    if (polynomial_is_assigned_and_non_zero(h[0], m)) {
      lp_polynomial_hash_set_insert(N, h[0]);
      ret = FOUND;
      goto cleanup;
    }
    // ... otherwise there is no need to add it to F (because it has no var).
  }
  // all h[i]'s top variable is var, thus none can be excluding
  for (; i < r; i++) {
    if (track_lc_branch_condition(h[i], m, var, 1, M, N)) {
      assert(lp_polynomial_top_variable(h[i]) == var);
      lp_polynomial_heap_push(F, h[i]);
      ret = PROCESSED;
      goto cleanup;
    }
  }

  // (ret == NOT_APPLICABLE): all lc are zero for m
  // I don't think this should happen // TODO check it
  lp_polynomial_heap_push(F, p1);

  cleanup:
  lp_polynomial_delete(p1);
  for (int j = 0; j < r; ++j) {
    lp_polynomial_delete(h[j]);
  }
  free(h);

  return ret;
}

/** tries to reduce G wrt. to p2 by finding a gcd with one element from G */
static
explain_result_t explain_pQ(const lp_polynomial_t *p2,
                            lp_polynomial_heap_t *F, lp_polynomial_heap_t *G,
                            lp_polynomial_hash_set_t *M, lp_polynomial_hash_set_t *N,
                            const lp_assignment_t *m, lp_variable_t var) {

  assert(!lp_polynomial_heap_is_empty(G));

  const lp_polynomial_t *p1 = lp_polynomial_heap_peek(G);

  size_t r;
  lp_polynomial_t **h = srs(p1, p2, &r);

  explain_result_t ret = NOT_APPLICABLE;
  for (size_t i = 0; i < r; i++) {
    if (track_lc_branch_condition(h[i], m, var, 1, M, N)) {
      if (lp_polynomial_top_variable(h[i]) != var) {
        assert(i == 0);
        lp_polynomial_delete(lp_polynomial_heap_pop(G));
      }
      lp_polynomial_t *rem = pquo(p2, h[i], var);
      // did we find an excluding polynomial?
      if (polynomial_is_assigned_and_non_zero(rem, m)) {
        if (!lp_polynomial_is_constant(rem)) { lp_polynomial_hash_set_insert(N, rem); }
        ret = FOUND;
      } else {
        assert(lp_polynomial_top_variable(rem) == var);
        lp_polynomial_heap_push(F, rem);
        ret = PROCESSED;
      }
      lp_polynomial_delete(rem);
      goto cleanup;
    }
  }

  // (ret == NOT_APPLICABLE): all lc are zero for m
  // I don't think this should happen (ret == NOT_APPLICABLE) // TODO check it

  cleanup:
  for (int j = 0; j < r; ++j) {
    lp_polynomial_delete(h[j]);
  }
  free(h);

  return ret;
}

static inline
explain_result_t exclude_p(const lp_polynomial_t *p2,
                           lp_polynomial_heap_t *F, lp_polynomial_heap_t *G,
                           lp_polynomial_hash_set_t *M, lp_polynomial_hash_set_t *N,
                           const lp_assignment_t *m, lp_variable_t var) {

  // this is a set of negative condition, thus adding to the positive side-conditions to make it end up with the negative literals
  exclude_coefficient(p2, m, var, M);
  return FOUND;
}

/** tries to reduce elements of G */
static
explain_result_t explain_Q(lp_polynomial_heap_t *F, lp_polynomial_heap_t *G,
                           lp_polynomial_hash_set_t *M, lp_polynomial_hash_set_t *N,
                           const lp_assignment_t *m, lp_variable_t var) {

  for (int i = 0; i < lp_polynomial_heap_size(G); ++i) {
    const lp_polynomial_t *g = lp_polynomial_heap_at(G, i);
    assert (lp_polynomial_top_variable(g) == var);
    lp_polynomial_t *lc_g = lc(g, var);
    if (polynomial_is_zero_m(lc_g, m)) {
      lp_polynomial_hash_set_insert(M, lc_g);
      lp_polynomial_heap_remove(G, g);

      explain_result_t ret;
      lp_polynomial_t *red_g = red(g, var);
      if (polynomial_is_assigned_and_zero(red_g, m)) {
        // can only be the case when g = lc*var^d + rem (d > 0 and rem has no var)
        if (!lp_polynomial_is_constant(red_g)) { lp_polynomial_hash_set_insert(M, red_g); }
        ret = FOUND;
      } else {
        if (lp_polynomial_top_variable(red_g) == var) { lp_polynomial_heap_push(G, red_g); }
        ret = PROCESSED;
      }
      lp_polynomial_delete(red_g);
      lp_polynomial_delete(lc_g);
      return ret;
    }
    // no need to add lc_g to N here // TODO check it
    lp_polynomial_delete(lc_g);
  }

  return NOT_APPLICABLE;
}

static inline
explain_result_t exclude_q(lp_polynomial_heap_t *F, lp_polynomial_heap_t *G,
                           lp_polynomial_hash_set_t *M, lp_polynomial_hash_set_t *N,
                           const lp_assignment_t *m, lp_variable_t var) {
  // very unlikely case (make sure that the core is minimized)
  lp_polynomial_t *prod = lp_polynomial_heap_pop(G);
  while (!lp_polynomial_heap_is_empty(G) &&
         lp_polynomial_top_variable(lp_polynomial_heap_peek(G)) == var) {
    lp_polynomial_mul(prod, prod, lp_polynomial_heap_peek(G));
    lp_polynomial_delete(lp_polynomial_heap_pop(G));
  }
  // when the result is constant, then it must be zero
  assert(!lp_polynomial_is_constant(prod) || lp_polynomial_is_zero(prod));

  // this is a set of negative condition, thus adding to the positive side-conditions to make it end up with the negative literals
  exclude_coefficient(prod, m, var, M);
  lp_polynomial_delete(prod);
  return FOUND;
}

static inline
lp_variable_t top_variable(const lp_polynomial_t *p) {
  return (p == NULL) ? lp_variable_null : lp_polynomial_top_variable(p);
}

/*
 * based on algorithm RegSer from Wang's book
 * var variable to eliminate
 * F list of positive polynomials (in var)
 * G list of negative polynomials (in var)
 * M list of positive side conditions (and negative conditions)
 * N list of negative side conditions (and positive conditions)
 * m current assignment
 *
 * Remark: side conditions are returned inverted to clausify implication
 */
static
void split_reg_ser(lp_polynomial_heap_t *F, lp_polynomial_heap_t *G,
                   lp_polynomial_hash_set_t *M, lp_polynomial_hash_set_t *N,
                   const lp_assignment_t *m,  lp_variable_t var) {

  assert(var != lp_variable_null);
  assert(!lp_polynomial_heap_is_empty(F) || !lp_polynomial_heap_is_empty(G));

//    assert all(lv(m) < var for m in M) and all(lv(n) < var for n in N), "invalid side condition"
//    assert not check_ass(F, G, A, var), "assignment is not excluded"
//    assert check_ass(M, N, A, var), "side condition is excluded"

  explain_result_t rslt = NOT_APPLICABLE;
  do {
    assert(heap_contains_check_top_variable(F, var));
    assert(heap_contains_check_top_variable(G, var));

    if (top_variable(lp_polynomial_heap_peek(F)) == var) {
      lp_polynomial_t *p2 = lp_polynomial_heap_pop(F);
      assert(lp_polynomial_top_variable(p2) == var);

      // ensure that lc(p2, var) != 0 for later operations
      rslt = explain_p(p2, F, G, M, N, m, var);
      if (rslt != NOT_APPLICABLE) {
        lp_polynomial_delete(p2);
        continue;
      }

      assert(polynomial_lc_is_assigned_and_non_zero(p2, var, m));

      if (top_variable(lp_polynomial_heap_peek(F)) == var) {
        rslt = explain_pP(p2, F, G, M, N, m, var);
        assert(rslt != NOT_APPLICABLE);
      } else if (top_variable(lp_polynomial_heap_peek(G)) == var) {
        rslt = explain_pQ(p2, F, G, M, N, m, var);
        assert(rslt != NOT_APPLICABLE);
      } else {
        // p2 is the only polynomial with var
        assert(top_variable(lp_polynomial_heap_peek(G)) != var);
        rslt = exclude_p(p2, F, G, M, N, m, var);
        assert(rslt == FOUND);
      }
      lp_polynomial_delete(p2);
    } else {
      assert(!lp_polynomial_heap_is_empty(G) && lp_polynomial_top_variable(lp_polynomial_heap_peek(G)) == var);
      rslt = explain_Q(F, G, M, N, m, var);
      if (rslt != NOT_APPLICABLE)
        continue;
      rslt = exclude_q(F, G, M, N, m, var);
      assert(rslt == FOUND);
    }
    assert(rslt != NOT_APPLICABLE);
  } while (rslt != FOUND);
}

static
int compare_polynomial_inverse_degree(const lp_polynomial_t *p1, const lp_polynomial_t *p2) {
  assert(lp_polynomial_context_equal(lp_polynomial_get_context(p1), lp_polynomial_get_context(p2)));
  int cmp = lp_variable_order_cmp(lp_polynomial_get_context(p1)->var_order,
                                  lp_polynomial_top_variable(p1),
                                  lp_polynomial_top_variable(p2));
  if (cmp) { return cmp; }
  return -((int)lp_polynomial_degree(p1) - (int)lp_polynomial_degree(p2));
}

static
void lp_polynomial_move_push_hash_set(lp_polynomial_heap_t *heap, lp_polynomial_hash_set_t *hset) {
  lp_polynomial_hash_set_close(hset);
  for (size_t i = 0; i < hset->size; ++i) {
    lp_polynomial_heap_push_move(heap, hset->data[i]);
  }
}

static
void explain_multi(const lp_data_t *lp_data,
                   lp_polynomial_hash_set_t *eq, lp_polynomial_hash_set_t *ne,
                   lp_polynomial_hash_set_t *e_eq, lp_polynomial_hash_set_t *e_ne) {

  const lp_assignment_t *m = lp_data->lp_assignment;

  assert(eq->closed && ne->closed);
  assert(eq->size > 0 || ne->size > 0);
  assert(!e_eq->closed && !e_ne->closed);

  if (ctx_trace_enabled(lp_data->plugin_ctx, "ff::explain")) {
    ctx_trace_printf(lp_data->plugin_ctx, "explain_multi (\n  ");
    lp_polynomial_hash_set_print(eq, ctx_trace_out(lp_data->plugin_ctx));
    ctx_trace_printf(lp_data->plugin_ctx, ", \n  ");
    lp_polynomial_hash_set_print(ne, ctx_trace_out(lp_data->plugin_ctx));
    ctx_trace_printf(lp_data->plugin_ctx, "\n)\n");
  }

  const lp_polynomial_context_t *ctx =  lp_data->lp_ctx;

  lp_polynomial_heap_t
      *F = lp_polynomial_heap_new(compare_polynomial_inverse_degree),
      *G = lp_polynomial_heap_new(compare_polynomial_inverse_degree);

  // moves all polynomials from the hashset to the heap
  lp_polynomial_move_push_hash_set(F, eq);
  lp_polynomial_move_push_hash_set(G, ne);

  lp_variable_t var = lp_variable_order_max(ctx->var_order,
    !lp_polynomial_heap_is_empty(F) ? lp_polynomial_top_variable(lp_polynomial_heap_peek(F)) : lp_variable_null,
    !lp_polynomial_heap_is_empty(G) ? lp_polynomial_top_variable(lp_polynomial_heap_peek(G)) : lp_variable_null
  );
  assert(!lp_assignment_is_set(m, var));
  assert(heap_contains_check_top_variable(F, var));
  assert(heap_contains_check_top_variable(G, var));

  split_reg_ser(F, G, e_ne, e_eq, m, var);

  lp_polynomial_hash_set_close(e_eq);
  lp_polynomial_hash_set_close(e_ne);

  if (ctx_trace_enabled(lp_data->plugin_ctx, "ff::explain")) {
    ctx_trace_printf(lp_data->plugin_ctx, "explain_multi () => \n  ");
    lp_polynomial_hash_set_print(e_eq, ctx_trace_out(lp_data->plugin_ctx));
    ctx_trace_printf(lp_data->plugin_ctx, ", \n  ");
    lp_polynomial_hash_set_print(e_ne, ctx_trace_out(lp_data->plugin_ctx));
    ctx_trace_printf(lp_data->plugin_ctx, "\n");
  }

  lp_polynomial_heap_delete(F);
  lp_polynomial_heap_delete(G);
}

static inline
term_t lp_polynomial_to_term(ff_plugin_t* ff, const lp_polynomial_t* p) {
  return lp_polynomial_to_yices_term(ff->lp_data, p, ff->ctx->tm->terms, &ff->buffer);
}

void ff_plugin_explain_conflict(ff_plugin_t* ff, const ivector_t* core, const ivector_t* lemma_reasons, ivector_t* conflict) {
  const mcsat_trail_t* trail = ff->ctx->trail;
  variable_db_t* var_db = ff->ctx->var_db;

  // TODO check if gcd_simplify_zero works
  // TODO check if sorting the vectors helps

  if (ctx_trace_enabled(ff->ctx, "ff::explain")) {
    ctx_trace_printf(ff->ctx, "ff_plugin_explain_conflict()\n");
    uint32_t i;
    int_mset_t variables;
    int_mset_construct(&variables, variable_null);
    for (i = 0; i < core->size; ++ i) {
      term_t core_i_t = variable_db_get_term(var_db, core->data[i]);
      ff_plugin_get_constraint_variables(ff, core_i_t, &variables);
      ctx_trace_printf(ff->ctx, "core[%u] = ", i);
      ctx_trace_term(ff->ctx, core_i_t);
    }
    trail_print(ff->ctx->trail, ctx_trace_out(ff->ctx));
    ivector_t* variables_list = int_mset_get_list(&variables);
    for (i = 0; i < variables_list->size; ++ i) {
      variable_t var = variables_list->data[i];
      if (trail_has_value(ff->ctx->trail, var)) {
        const mcsat_value_t* v = trail_get_value(ff->ctx->trail, var);
        variable_db_print_variable(var_db, var, ctx_trace_out(ff->ctx));
        ctx_trace_printf(ff->ctx, " -> ");
        mcsat_value_print(v, ctx_trace_out(ff->ctx));
        ctx_trace_printf(ff->ctx, "\n");
      }
    }
    int_mset_destruct(&variables);
  }

  lp_polynomial_hash_set_t pos;
  lp_polynomial_hash_set_t neg;

  lp_polynomial_hash_set_construct(&pos);
  lp_polynomial_hash_set_construct(&neg);

  for (uint32_t core_i = 0; core_i < core->size; ++ core_i) {
    variable_t constraint_var = core->data[core_i];
    assert(trail_has_value(trail, constraint_var));
    const poly_constraint_t* constraint = poly_constraint_db_get(ff->constraint_db, constraint_var);

    // get poly, condition, and negation status
    const lp_polynomial_t* p = poly_constraint_get_polynomial(constraint);
    lp_sign_condition_t sgn_condition = poly_constraint_get_sign_condition(constraint);
    bool negated = !trail_get_boolean_value(trail, constraint_var);

    // get the conflict variable as lp_variable_t
    variable_t conflict_var = ff->conflict_variable;
    assert(conflict_var != variable_null);
    term_t t = variable_db_get_term(var_db, conflict_var);
    lp_variable_t x = lp_data_get_lp_variable_from_term(ff->lp_data, t);

    assert(lp_polynomial_top_variable(p) == x);
    assert(sgn_condition == LP_SGN_EQ_0 || sgn_condition == LP_SGN_NE_0);
    bool is_pos = (!negated && (sgn_condition == LP_SGN_EQ_0)) || (negated && (sgn_condition == LP_SGN_NE_0));
    lp_polynomial_hash_set_insert(is_pos ? &pos : &neg, p);
  }

  // not used yet
  assert(lemma_reasons->size == 0);

  lp_polynomial_hash_set_close(&pos);
  lp_polynomial_hash_set_close(&neg);

  // TODO update TRACE printing here

  lp_polynomial_hash_set_t e_eq;
  lp_polynomial_hash_set_t e_ne;

  lp_polynomial_hash_set_construct(&e_eq);
  lp_polynomial_hash_set_construct(&e_ne);

  size_t cnt_pos = lp_polynomial_hash_set_size(&pos);
  size_t cnt_neg = lp_polynomial_hash_set_size(&neg);
  assert(cnt_pos + cnt_neg > 0);

  lp_assignment_t *m = ff->lp_data->lp_assignment;

  if (cnt_pos + cnt_neg > 1) {
    explain_multi(ff->lp_data, &pos, &neg, &e_eq, &e_ne);
  } else if (cnt_pos == 1) {
    explain_single(ff->lp_data, pos.data[0], &e_ne);
  } else if (cnt_neg == 1) {
    explain_single(ff->lp_data, neg.data[0], &e_ne);
  }

  // assert that the current assignment is excluded (all ne must be = 0 and eq must be != 0)
  assert(check_assignment_cube(&e_ne, &e_eq, m));

  // Add the explanation to the conflict
  lp_polynomial_hash_set_close(&e_eq);
  for (size_t i = 0; i < e_eq.size; ++i) {
    term_t t = lp_polynomial_to_term(ff, e_eq.data[i]);
    ivector_push(conflict, pos_term(t));
  }

  lp_polynomial_hash_set_close(&e_ne);
  for (size_t i = 0; i < e_ne.size; ++i) {
    term_t t = lp_polynomial_to_term(ff, e_ne.data[i]);
    ivector_push(conflict, neg_term(t));
  }

  // Add the core to the conflict
  for (uint32_t core_i = 0; core_i < core->size; ++ core_i) {
    variable_t constraint_var = core->data[core_i];
    term_t constraint_term = variable_db_get_term(var_db, constraint_var);
    assert(trail_has_value(trail, constraint_var));
    bool constraint_value = trail_get_boolean_value(trail, constraint_var);
    if (!constraint_value) {
      constraint_term = opposite_term(constraint_term);
    }
    ivector_push(conflict, constraint_term);
  }

  // clean-up
  lp_polynomial_hash_set_destruct(&pos);
  lp_polynomial_hash_set_destruct(&neg);
  lp_polynomial_hash_set_destruct(&e_eq);
  lp_polynomial_hash_set_destruct(&e_ne);
}
