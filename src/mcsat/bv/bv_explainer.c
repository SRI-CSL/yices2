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

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "bv_explainer.h"

#include "bv_evaluator.h"
#include "bv_utils.h"

#include "mcsat/variable_db.h"
#include "mcsat/tracing.h"
#include "mcsat/utils/int_mset.h"
#include "mcsat/eq/equality_graph.h"

#include "explain/arith.h"
#include "explain/eq_ext_con.h"
#include "explain/full_bv_sat.h"
#include "explain/full_bv_trivial.h"

#include "yices.h"
#include <inttypes.h>

void bv_subexplainer_construct(bv_subexplainer_t* exp, const char* name, plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {

  char name_buffer[100];

  exp->ctx = ctx;
  exp->wlm = wlm;
  exp->eval = eval;

  exp->name = name;

  snprintf(name_buffer, 100, "%s.conflict", name);
  exp->stat_explain_conflict_calls = statistics_new_int(ctx->stats, name_buffer);
  snprintf(name_buffer, 100, "%s.propagation", name);
  exp->stat_explain_propagation_calls = statistics_new_int(ctx->stats, name_buffer);

  exp->destruct                = NULL;
  exp->can_explain_conflict    = NULL;
  exp->explain_conflict        = NULL;
  exp->can_explain_propagation = NULL;
  exp->explain_propagation     = NULL;
}

void bv_explainer_construct(bv_explainer_t* exp, plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {

  exp->ctx = ctx;
  exp->tm = ctx->tm;
  exp->wlm = wlm;
  exp->eval = eval;

  init_ivector(&exp->tmp_conflict_vec, 0);

  bool use_yices = true;

  // Add all the explainers
  init_pvector(&exp->subexplainers, 0);
  pvector_push(&exp->subexplainers, eq_ext_con_new(ctx, wlm, eval));
  pvector_push(&exp->subexplainers, arith_new(ctx, wlm, eval));
  if (use_yices) {
    pvector_push(&exp->subexplainers, full_bv_sat_new(ctx, wlm, eval));
  } else {
    pvector_push(&exp->subexplainers, full_bv_trivial_new(ctx, wlm, eval));
  }
}

void bv_explainer_destruct(bv_explainer_t* exp) {
  uint32_t i;

  delete_ivector(&exp->tmp_conflict_vec);

  // Delete all the sub-explainers
  for(i = 0; i < exp->subexplainers.size; ++ i) {
    bv_subexplainer_t* sub = exp->subexplainers.data[i];
    if (sub->destruct != NULL) {
      sub->destruct(sub);
    }
    safe_free(sub);
  }
  delete_pvector(&exp->subexplainers);
}

/**
 * Normalize the conflict for the following cases
 * - Boolean equalities (must evaluate to true)
 */
void bv_explainer_normalize_conflict(bv_explainer_t* exp, ivector_t* conflict_out) {
  uint32_t i;

  term_table_t* terms = exp->ctx->terms;
  const variable_db_t* var_db = exp->ctx->var_db;
  const mcsat_trail_t* trail = exp->ctx->trail;

  ivector_reset(&exp->tmp_conflict_vec);

  for (i = 0; i < conflict_out->size; ++ i) {
    term_t literal = conflict_out->data[i];
    assert(term_type_kind(terms, literal) == BOOL_TYPE);
    term_kind_t literal_kind = term_kind(terms, literal);

    if (literal_kind == EQ_TERM) {
      term_t literal_pos = unsigned_term(literal);
      variable_t literal_var = variable_db_get_variable_if_exists(var_db, literal_pos);

      // Literal evaluates to true?
      bool evaluates_to_true = literal_var != variable_null &&
          trail_has_value(trail, literal_var) &&
          trail_get_value(trail, literal_var)->b;

      if (evaluates_to_true) {
        // Evaluates to true, good conflict
        ivector_push(&exp->tmp_conflict_vec, literal);
      } else {
        // The individual terms must evaluate to true
        composite_term_t* eq_desc = eq_term_desc(terms, literal_pos);
        term_t lhs = eq_desc->arg[0];
        term_t rhs = eq_desc->arg[1];
        if (is_boolean_term(terms, lhs)) {
          assert(is_boolean_term(terms, rhs));
          // Negate lhs if false
          uint32_t lhs_eval_level = 0;
          const mcsat_value_t* lhs_value = bv_evaluator_evaluate_term(exp->eval, lhs, &lhs_eval_level);
          assert(lhs_value->type == VALUE_BOOLEAN);
          if (!lhs_value->b) {
            lhs = opposite_term(lhs);
          }
          // Negate rhs if false
          uint32_t rhs_eval_level = 0;
          const mcsat_value_t* rhs_value = bv_evaluator_evaluate_term(exp->eval, rhs, &rhs_eval_level);
          assert(rhs_value->type == VALUE_BOOLEAN);
          if (!rhs_value->b) {
            rhs = opposite_term(rhs);
          }
          // Add the literals to the explanations
          ivector_push(&exp->tmp_conflict_vec, lhs);
          ivector_push(&exp->tmp_conflict_vec, rhs);
        } else {
          // Not a Boolean equality, just keep it
          ivector_push(&exp->tmp_conflict_vec, literal);
        }
      }
    } else {
      ivector_push(&exp->tmp_conflict_vec, literal);
    }
  }

  ivector_swap(conflict_out, &exp->tmp_conflict_vec);
  ivector_reset(&exp->tmp_conflict_vec);
}

void bv_explainer_check_conflict(bv_explainer_t* exp, const ivector_t* conflict) {
  context_t* ctx = yices_new_context(NULL);
  uint32_t i;
  for (i = 0; i < conflict->size; ++ i) {
    yices_assert_formula(ctx, conflict->data[i]);
  }
  smt_status_t result = yices_check_context(ctx, NULL);
  (void) result;
  assert(result == STATUS_UNSAT);
  yices_free_context(ctx);
}

void print_counters(bv_explainer_t* exp){
  FILE* out = ctx_trace_out(exp->ctx);
  bv_subexplainer_t* subexplainer = NULL;
  for (uint32_t i = 0; i < exp->subexplainers.size; ++ i) {
    subexplainer = exp->subexplainers.data[i];
    fprintf(out, "%s: %d conflicts, %d propas; ",
            subexplainer->name,
            (*subexplainer->stat_explain_conflict_calls),
            (*subexplainer->stat_explain_propagation_calls));
  }
}

void bv_explainer_get_conflict(bv_explainer_t* exp, const ivector_t* conflict_in, variable_t conflict_var, ivector_t* conflict_out) {

  // Get the explainer to use
  uint32_t i = 0;
  bv_subexplainer_t* subexplainer = NULL;
  for (i = 0; i < exp->subexplainers.size; ++ i) {
    subexplainer = exp->subexplainers.data[i];
    if (subexplainer->can_explain_conflict(subexplainer, conflict_in, conflict_var)) {
      break;
    }
  }

  // BD: try to remove a false alarm produced by
  // the clang static analyzer
  assert(subexplainer != NULL);

  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(exp->ctx);
    fprintf(out, "subtheory %s\n", subexplainer->name);
  }

  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict::count"))
    print_counters(exp);
  
  // Explain it
  (*subexplainer->stat_explain_conflict_calls) ++;
  subexplainer->explain_conflict(subexplainer, conflict_in, conflict_var, conflict_out);

  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict::count")) {
    FILE* out = ctx_trace_out(exp->ctx);
    fprintf(out, "Done by %s\n", subexplainer->name);
  }
  
  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict::check")) {
    static int conflict_count = 0;
    conflict_count ++;
    bv_explainer_check_conflict(exp, conflict_out);
  }

  // Normalize conflict
  bv_explainer_normalize_conflict(exp, conflict_out);

  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict::check")) {
    bv_explainer_check_conflict(exp, conflict_out);
  }
}

term_t bv_explainer_explain_propagation(bv_explainer_t* exp, variable_t x, const ivector_t* reasons_in, ivector_t* reasons_out) {

  // Get the explainer to use
  uint32_t i = 0;
  bv_subexplainer_t* subexplainer = NULL;
  term_t subst = NULL_TERM;

  // Until someone explains (full_sat always explains in the end)
  for (; subst == NULL_TERM; ++ i) {

    // Find someone willing to explain
    for (; i < exp->subexplainers.size; ++ i) {
      subexplainer = exp->subexplainers.data[i];
      if (subexplainer->can_explain_propagation(subexplainer, reasons_in, x)) {
        break;
      }
    }

    // BD: remove a false alarm produced by the clang static analyzer
    assert(subexplainer != NULL);

    if (ctx_trace_enabled(exp->ctx, "mcsat::bv::explain")) {
      FILE* out = ctx_trace_out(exp->ctx);
      fprintf(out, "subtheory %s\n", subexplainer->name);
    }

    if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict::count"))
      print_counters(exp);

    // Try to explain it (might fail)
    (*subexplainer->stat_explain_propagation_calls) ++;
    subst = subexplainer->explain_propagation(subexplainer, reasons_in, x, reasons_out);

    if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict::count")) {
      FILE* out = ctx_trace_out(exp->ctx);
      fprintf(out, "Done by %s\n", subexplainer->name);
    }
    
  }

  // Normalize the explanation
  bv_explainer_normalize_conflict(exp, reasons_out);

  return subst;
}

