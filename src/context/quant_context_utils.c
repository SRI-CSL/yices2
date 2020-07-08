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
 * CONTEXT UTILITIES FOR QUANTIFIERS
 */

#include "context/quant_context_utils.h"
#include "context/context_simplifier.h"
#include "context/context_utils.h"
#include "context/internalization_codes.h"
#include "context/ite_flattener.h"
#include "terms/term_utils.h"
#include "utils/memalloc.h"

#include "api/yices_globals.h"




/*
 * Top-level equality assertion (eq t1 t2):
 * - if tt is true, assert (t1 == t2)
 *   if tt is false, assert (t1 != t2)
 */
static void quant_assert_toplevel_eq(context_t *ctx, composite_term_t *eq, bool tt) {
  occ_t u1, u2;
  egraph_t *egraph;
  literal_t l;

  assert(eq->arity == 2);

  if (is_boolean_term(ctx->terms, eq->arg[0])) {
    assert(is_boolean_term(ctx->terms, eq->arg[1]));
    assert_toplevel_iff(ctx, eq->arg[0], eq->arg[1], tt);
  } else {
    u1 = internalize_to_eterm(ctx, eq->arg[0]);
    u2 = internalize_to_eterm(ctx, eq->arg[1]);

    if (! context_has_egraph(ctx)) {
      longjmp(ctx->env, INTERNAL_ERROR);
    }
    egraph = ctx->egraph;

    if (egraph->decision_level == egraph->base_level) {
      if (tt) {
        egraph_assert_eq_axiom(egraph, u1, u2);
      } else {
        egraph_assert_diseq_axiom(egraph, u1, u2);
      }
    } else {
      l = egraph_make_eq(egraph, u1, u2);
      if (tt) {
        add_unit_clause(ctx->core, l);
      } else {
        add_unit_clause(ctx->core, not(l));
      }
    }

  }
}

/*
 * Top-level predicate: (p t_1 .. t_n)
 * - if tt is true: assert (p t_1 ... t_n)
 * - if tt is false: assert (not (p t_1 ... t_n))
 */
void quant_assert_toplevel_apply(context_t *ctx, composite_term_t *app, bool tt) {
  occ_t *a;
  uint32_t i, n;
  egraph_t *egraph;
  literal_t l;

  assert(app->arity > 0);

  n = app->arity;
  a = alloc_istack_array(&ctx->istack, n);
  for (i=0; i<n; i++) {
    a[i] = internalize_to_eterm(ctx, app->arg[i]);
  }

  if (! context_has_egraph(ctx)) {
    longjmp(ctx->env, INTERNAL_ERROR);
  }
  egraph = ctx->egraph;

  if (egraph->decision_level == egraph->base_level) {
    if (tt) {
      egraph_assert_pred_axiom(ctx->egraph, a[0], n-1, a+1);
    } else {
      egraph_assert_notpred_axiom(ctx->egraph, a[0], n-1, a+1);
    }
  } else {
    l = egraph_make_pred(egraph, a[0], n-1, a+1);
    if (tt) {
      add_unit_clause(ctx->core, l);
    } else {
      add_unit_clause(ctx->core, not(l));
    }
  }

  free_istack_array(&ctx->istack, a);
}

/*
 * Generic (distinct t1 .. t_n)
 * - if tt: assert (distinct t_1 ... t_n)
 * - otherwise: assert (not (distinct t_1 ... t_n))
 */
static void quant_assert_toplevel_distinct(context_t *ctx, composite_term_t *distinct, bool tt) {
  uint32_t i, n;
  int32_t *a;
  egraph_t *egraph;
  literal_t l;

  n = distinct->arity;
  assert(n >= 2);

  a = alloc_istack_array(&ctx->istack, n);

  if (context_has_egraph(ctx)) {
    // forward the assertion to the egraph
    for (i=0; i<n; i++) {
      a[i] = internalize_to_eterm(ctx, distinct->arg[i]);
    }

    if (! context_has_egraph(ctx)) {
      longjmp(ctx->env, INTERNAL_ERROR);
    }
    egraph = ctx->egraph;

    if (egraph->decision_level == egraph->base_level) {
      if (tt) {
        egraph_assert_distinct_axiom(egraph, n, a);
      } else {
        egraph_assert_notdistinct_axiom(egraph, n, a);
      }
    } else {
      l = egraph_make_distinct(egraph, n, a);
      if (tt) {
        add_unit_clause(ctx->core, l);
      } else {
        add_unit_clause(ctx->core, not(l));
      }
    }

  } else {
    longjmp(ctx->env, INTERNAL_ERROR);
  }

  free_istack_array(&ctx->istack, a);
}


/*
 * Assert toplevel instance formula t:
 * - t is a boolean term (or the negation of a boolean term)
 */
void quant_assert_toplevel_formula(context_t *ctx, term_t t) {
  term_table_t *terms;
  int32_t code;
  bool tt;

  assert(is_boolean_term(ctx->terms, t));

  tt = is_pos_term(t);
  t = unsigned_term(t);

  if (! intern_tbl_root_is_mapped(&ctx->intern, t)) {
    // make t to be a root in the internalization table and map to true
    intern_tbl_map_root(&ctx->intern, t, bool2code(tt));
  }

  /*
   * Now: t is a root and has positive polarity
   * - tt indicates whether we assert t or (not t):
   *   tt true: assert t
   *   tt false: assert (not t)
   */
  terms = ctx->terms;
  switch (term_kind(terms, t)) {
  case CONSTANT_TERM:
  case UNINTERPRETED_TERM:
    // should be eliminated by flattening
    code = INTERNAL_ERROR;
    goto abort;

  case ITE_TERM:
  case ITE_SPECIAL:
    assert_toplevel_ite(ctx, ite_term_desc(terms, t), tt);
    break;

  case OR_TERM:
    assert_toplevel_or(ctx, or_term_desc(terms, t), tt);
    break;

  case XOR_TERM:
    assert_toplevel_xor(ctx, xor_term_desc(terms, t), tt);
    break;

  case EQ_TERM:
    quant_assert_toplevel_eq(ctx, eq_term_desc(terms, t), tt);
    break;

  case APP_TERM:
    quant_assert_toplevel_apply(ctx, app_term_desc(terms, t), tt);
    break;

  case DISTINCT_TERM:
    quant_assert_toplevel_distinct(ctx, distinct_term_desc(terms, t), tt);
    break;

  case VARIABLE:
    printf("Found variable here\n");
    assert(0);
    code = FREE_VARIABLE_IN_FORMULA;
    goto abort;

  default:
    code = INTERNAL_ERROR;
    goto abort;
  }

  return;

 abort:
  longjmp(ctx->env, code);
}

