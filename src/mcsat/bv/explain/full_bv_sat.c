/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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

#include "full_bv_sat.h"

#include "mcsat/tracing.h"
#include "mcsat/value.h"
#include "mcsat/bv/bv_utils.h"
#include "mcsat/mcsat_types.h"
#include "mcsat/variable_db.h"
#include "mcsat/utils/substitution.h"

#include "utils/int_vectors.h"
#include "utils/int_array_sort2.h"

#include "context/context.h"

#include "terms/term_manager.h"

#include "yices.h"
#include "api/yices_api_lock_free.h"

#include <inttypes.h>

/** Solver for solving cores with assumptions */
typedef struct {

  /** Whether to do incremental solving */
  bool incremental;

  /** The substitution */
  substitution_t subst;

  /** The terms to assign (old terms, not new) */
  ivector_t vars_to_assign;

  /** MCSAT plugin context */
  plugin_context_t* ctx;

  /** Yices context */
  context_t* yices_ctx;

} bb_sat_solver_t;


/*
 * BUG FIX:
 * - The Yices API maintains globals lists of configs and contexts to delete them all when
 *   yices_exit() is called.
 * - This means that yices_free_context/yices_free_config are not re-entrant.
 * - It's not safe to use yices_new_config, yices_new_context, yice_free_context, yices_free_config here.
 * - We must allocate and free the context locally.
 */
static context_t *new_yices_bv_context(plugin_context_t *ctx) {
  context_t *yctx;

  yctx = safe_malloc(sizeof(context_t));
  init_context(yctx, ctx->terms, QF_BV, CTX_MODE_PUSHPOP, CTX_ARCH_BV, false);
  // default options
  enable_variable_elimination(yctx);
  enable_bvarith_elimination(yctx);
  enable_diseq_and_or_flattening(yctx);

  return yctx;
}

static void free_yices_bv_context(context_t *yctx) {
  delete_context(yctx);
  safe_free(yctx);
}


void bb_sat_solver_construct(bb_sat_solver_t* solver, plugin_context_t* ctx, bool incremental) {
  substitution_construct(&solver->subst, ctx->tm, ctx->tracer);
  init_ivector(&solver->vars_to_assign, 0);
  solver->ctx = ctx;
  solver->incremental = incremental;

  // Create an instance of Yices
  // See above. we can't use yices_new_context
  solver->yices_ctx = new_yices_bv_context(ctx);

  // Incremental, do a push
  if (incremental) {
    yices_push(solver->yices_ctx);
  }
}

void bb_sat_solver_destruct(bb_sat_solver_t* solver) {
  substitution_destruct(&solver->subst);
  delete_ivector(&solver->vars_to_assign);

  // Delete the yices instance
  free_yices_bv_context(solver->yices_ctx);
}

void bb_sat_solver_reset(bb_sat_solver_t* solver) {
  if (solver->incremental) {
    yices_pop(solver->yices_ctx);
    yices_push(solver->yices_ctx);
    substitution_destruct(&solver->subst);
    substitution_construct(&solver->subst, solver->ctx->tm, solver->ctx->tracer);
    ivector_reset(&solver->vars_to_assign);
  } else {
    bb_sat_solver_destruct(solver);
    bb_sat_solver_construct(solver, solver->ctx, false);
  }
}


void bb_sat_solver_add_variable(bb_sat_solver_t* solver, variable_t var, bool with_value) {
  // Add new variable to substitute
  term_t var_term = variable_db_get_term(solver->ctx->var_db, var);
  if (ctx_trace_enabled(solver->ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(solver->ctx);
    fprintf(out, "Variable: ");
    ctx_trace_term(solver->ctx, var_term);
  }
  if (!substitution_has_term(&solver->subst, var_term)) {
    // Make a fresh variable if not already a variable
    term_t var_fresh;
    term_kind_t kind = term_kind(solver->yices_ctx->terms, var_term);
    if (kind != UNINTERPRETED_TERM) {
      type_t var_type = _o_yices_type_of_term(var_term);
      var_fresh = _o_yices_new_uninterpreted_term(var_type);
    } else {
      var_fresh = var_term;
    }
    substitution_add(&solver->subst, var_term, var_fresh);
    // If to be assigned, remember it
    if (with_value) {
      ivector_push(&solver->vars_to_assign, var);
    }
  }
}

void bb_sat_solver_assert_term(bb_sat_solver_t* solver, variable_t assertion_term) {
  assertion_term = substitution_run_fwd(&solver->subst, assertion_term, 0);
  if (ctx_trace_enabled(solver->ctx, "mcsat::bv::conflict")) {
    FILE* out = trace_out(solver->yices_ctx->trace);
    ctx_trace_term(solver->ctx, assertion_term);
    fprintf(out, "  previously \n");
    ctx_trace_term(solver->ctx, assertion_term);
  }
  _o_yices_assert_formula(solver->yices_ctx, assertion_term);
}

/**
 * Run the substitution and assert (with the same polarity as in MCSAT)
 */
void bb_sat_solver_assert_var(bb_sat_solver_t* solver, variable_t var) {
  term_t assertion_term = variable_db_get_term(solver->ctx->var_db, var);
  const mcsat_value_t* var_value = trail_get_value(solver->ctx->trail, var);
  assert(var_value->type == VALUE_BOOLEAN);
  if (!var_value->b) {
    assertion_term = opposite_term(assertion_term);
  }
  bb_sat_solver_assert_term(solver, assertion_term);
}

bool bb_sat_solver_cmp_var_by_trail_index(void *data, variable_t t1, variable_t t2) {
  const mcsat_trail_t* trail = data;
  assert(trail_has_value(trail, t1));
  assert(trail_has_value(trail, t2));
  return trail_get_index(trail, t1) < trail_get_index(trail, t2);
}

bool bb_sat_solver_cmp_bit_term(void *data, term_t t1, term_t t2) {
  term_table_t* terms = (term_table_t*) data;

  // don't care about sign, presume all different atoms
  t1 = unsigned_term(t1);
  t2 = unsigned_term(t2);

  term_kind_t t1_kind = term_kind(terms, t1);
  term_kind_t t2_kind = term_kind(terms, t2);
  if (t1_kind != t2_kind) {
    return t1_kind < t2_kind;
  }

  if (t1_kind == BIT_TERM) {
    term_t t1_arg = bit_term_arg(terms, t1);
    term_t t2_arg = bit_term_arg(terms, t2);
    if (t1_arg != t2_arg) {
      return t1_arg < t2_arg;
    }
    uint32_t t1_i = bit_term_index(terms, t1);
    uint32_t t2_i = bit_term_index(terms, t2);
    return t1_i < t2_i;
  }

  // Don't care about others
  return t1 < t2;
}

void bb_sat_solver_solve_and_get_core(bb_sat_solver_t* solver, term_vector_t* core) {

  uint32_t i, j, bit;

  plugin_context_t* ctx = solver->ctx;
  const variable_db_t* var_db = ctx->var_db;
  const mcsat_trail_t* trail = ctx->trail;
  term_manager_t* tm = solver->ctx->tm;
  term_table_t* terms = tm->terms;

  // Vector to store assumptions
  ivector_t assumptions;
  init_ivector(&assumptions, 0);

  // Sort variables to assign according to their trail index
  // int_array_sort2(solver->vars_to_assign.data, solver->vars_to_assign.size, (void*) solver->ctx->trail, bv_solver_cmp_var_by_trail_index);

  // Make assumptions
  for (i = 0; i < solver->vars_to_assign.size; ++ i) {
    // Variable and its value
    variable_t var = solver->vars_to_assign.data[i];
    const mcsat_value_t* var_value = trail_get_value(trail, var);
    assert(var_value->type == VALUE_BOOLEAN || var_value->type == VALUE_BV);
    // Get the term, and its substitution
    term_t var_term = variable_db_get_term(var_db, var);
    term_t var_term_subst = substitution_run_fwd(&solver->subst, var_term, 0);
    if (ctx_trace_enabled(ctx, "mcsat::bv::conflict")) {
      FILE* out = trace_out(solver->yices_ctx->trace);
      ctx_trace_term(ctx, var_term_subst);
      fprintf(out, "  -> ");
      mcsat_value_print(var_value, out);
      fprintf(out, "\n");
    }
    if (var_value->type == VALUE_BOOLEAN) {
      // Boolean variables, just add as assertion
      bool bool_value = var_value->b;
      if (!bool_value) var_term_subst = opposite_term(var_term_subst);
      ivector_push(&assumptions, var_term_subst);
    } else {
      // Bitvector variables
      const bvconstant_t* bv_value = &var_value->bv_value;
      // Assert individual bits
      for (bit = 0; bit < bv_value->bitsize; bit ++) {
        // Extract bit
        term_t bit_assertion = mk_bitextract(tm, var_term_subst, bit);
        // Assert appropriate value
        bool bool_value = bvconst_tst_bit(bv_value->data, bit);
        if (!bool_value) bit_assertion = opposite_term(bit_assertion);
        ivector_push(&assumptions, bit_assertion);
      }
    }
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Solving with assumptions: \n");
    for (i = 0; i < assumptions.size; ++ i) {
      ctx_trace_term(ctx, assumptions.data[i]);
    }
  }

  // Check the assumptions (should be unsat)
  smt_status_t status = _o_yices_check_context_with_assumptions(solver->yices_ctx, NULL, assumptions.size, assumptions.data);
  (void) status;
  assert(status == STATUS_UNSAT);

  // Get the unsat core
  int32_t ret = yices_get_unsat_core(solver->yices_ctx, core);
  (void) ret;
  assert(ret == 0);

  // Substitute the core back to internal
  for (i = 0; i < core->size; ++ i) {
    term_t t = core->data[i];
    t = substitution_run_bck(&solver->subst, t, 0);
    core->data[i] = t;
  }

  // Sort the core according to variable and bit
  int_array_sort2(core->data, core->size, (void*) solver->ctx->terms, bb_sat_solver_cmp_bit_term);

  if (ctx_trace_enabled(ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\n========\nCore from Yices2: \n");
    for (i = 0; i < core->size; ++ i) {
      ctx_trace_term(ctx, core->data[i]);
    }
  }

  // Now group the individual bit-selects into equalities over bit-arrays
  ivector_t grouped_core;
  ivector_t grouped_bits;
  bvconstant_t slice_value;
  init_ivector(&grouped_core, 0);
  init_ivector(&grouped_bits, 0);
  init_bvconstant(&slice_value);
  for (i = 0, j = 0; i < core->size; i = j) {
    term_t bit_term = core->data[i];
    if (term_kind(terms, bit_term) != BIT_TERM) {
      ivector_push(&grouped_core, bit_term);
      j = i + 1;
    } else {
      // Find the whole range i..j-1 with increasing bits
      term_t bit_arg = bit_term_arg(terms, bit_term);
      uint32_t bit_index = bit_term_index(terms, bit_term) + 1;
      j = i + 1;
      while (j < core->size) {
        select_term_t* bit_desc = bit_term_desc(terms, core->data[j]);
        if (bit_desc->arg != bit_arg) break;
        if (bit_desc->idx != bit_index) break;
        j ++; bit_index ++;
      }
      if (j == i + 1) {
        // If nothing to concatenate, just add it
        ivector_push(&grouped_core, bit_term);
      } else {
        // Concatenate bits and construct the value
        bvconstant_set_bitsize(&slice_value, j - i);
        for (bit = i; bit < j; ++ bit) {
          bit_term = core->data[bit];
          bool bit_is_negated = is_neg_term(bit_term);
          bit_term = unsigned_term(bit_term);
          ivector_push(&grouped_bits, bit_term);
          if (bit_is_negated) {
            bvconst_clr_bit(slice_value.data, bit - i);
          } else {
            bvconst_set_bit(slice_value.data, bit - i);
          }
        }
        // Make the terms
        term_t slice_term = mk_bvarray(tm, grouped_bits.size, grouped_bits.data);
        ivector_reset(&grouped_bits);
        term_t slice_value_term = mk_bv_constant(tm, &slice_value);
        term_t eq = mk_eq(tm, slice_term, slice_value_term);
        ivector_push(&grouped_core, eq);
      }
    }
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Simplified core: \n");
    for (i = 0; i < grouped_core.size; ++ i) {
      ctx_trace_term(ctx, grouped_core.data[i]);
    }
  }

  ivector_swap(&grouped_core, (ivector_t*) core);

  // Remove temps
  delete_ivector(&grouped_core);
  delete_ivector(&grouped_bits);
  delete_bvconstant(&slice_value);

  // Remove assumption vector
  delete_ivector(&assumptions);
}


typedef struct qf_bv_sat_s {

  /** Interfact of the subexplainer */
  bv_subexplainer_t super;

  /** Yices to for bitblasting and SAT solving */
  bb_sat_solver_t solver;

} full_bv_sat_t;

static
bool can_explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict, variable_t conflict_var) {
  // We can explain anything
  return true;
}

static
term_t explain(bv_subexplainer_t* super, const ivector_t* core_in, variable_t to_explain, ivector_t* core_out, bool is_conflict) {

  uint32_t i;

  full_bv_sat_t* this = (full_bv_sat_t*) super;

  const variable_db_t* var_db = super->ctx->var_db;
  const mcsat_trail_t* trail = super->ctx->trail;
  term_manager_t* tm = super->ctx->tm;
  bb_sat_solver_t* solver = &this->solver;

  // Reset the solver
  bb_sat_solver_reset(solver);

  // Get the assigned variables into a set and copy assertions into explanation
  for (i = 0; i < core_in->size; ++i) {
    // Get assigned variables
    variable_t atom_i_var = core_in->data[i];
    variable_list_ref_t list_ref = watch_list_manager_get_list_of(super->wlm, atom_i_var);
    if (ctx_trace_enabled(super->ctx, "mcsat::bv::conflict")) {
      FILE* out = ctx_trace_out(super->ctx);
      fprintf(out, "core[%"PRIu32"]: ", i);
      term_t atom_i_term = variable_db_get_term(var_db, atom_i_var);
      ctx_trace_term(solver->ctx, atom_i_term);
    }
    variable_t* atom_i_vars = watch_list_manager_get_list(super->wlm, list_ref);
    for (; *atom_i_vars != variable_null; atom_i_vars++) {
      variable_t var = *atom_i_vars;
      if (var != atom_i_var) {
        bool assign_value = (var != to_explain);
        bb_sat_solver_add_variable(solver, var, assign_value);
      }
    }
    // Copy into explanation
    const mcsat_value_t* atom_i_value = trail_get_value(trail, atom_i_var);
    assert(atom_i_value != NULL && atom_i_value->type == VALUE_BOOLEAN);
    term_t assertion = variable_db_get_term(var_db, atom_i_var);
    if (!atom_i_value->b) {
      assertion = opposite_term(assertion);
    }
    ivector_push(core_out, assertion);
  }

  // Now assert the core
  for (i = 0; i < core_in->size; ++i) {
    variable_t assertion_var = core_in->data[i];
    bb_sat_solver_assert_var(solver, assertion_var);
  }

  // Finally, if propagation, assert negation of it's value
  term_t propagated_value = NULL_TERM;
  term_t propagated_assert = NULL_TERM;
  if (!is_conflict) {
    const mcsat_value_t* value = trail_get_value(trail, to_explain);
    propagated_value = mcsat_value_to_term(value, tm);
    term_t x_term = variable_db_get_term(var_db, to_explain);
    propagated_assert = mk_eq(tm, x_term, propagated_value);
    propagated_assert = opposite_term(propagated_assert);
    bb_sat_solver_assert_term(solver, propagated_assert);
  }

  // Solve and get the core
  term_vector_t core;
  yices_init_term_vector(&core);
  bb_sat_solver_solve_and_get_core(solver, &core);

  // Copy over the core (except the
  for (i = 0; i < core.size; ++i) {
    term_t t = core.data[i];
    if (t != propagated_assert) {
      ivector_push(core_out, core.data[i]);
    }
  }

  // Delete stuff
  yices_delete_term_vector(&core);

  return propagated_value;
}

static
void explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict) {
  explain(this, conflict_core, conflict_var, conflict, true);\
}

static
bool can_explain_propagation(bv_subexplainer_t* this, const ivector_t* reasons, variable_t x) {
  return true;
}

static
term_t explain_propagation(bv_subexplainer_t* this, const ivector_t* reasons_in, variable_t x, ivector_t* reasons_out) {
  return explain(this, reasons_in, x, reasons_out, false);
}

static
void destruct(bv_subexplainer_t* super) {
  full_bv_sat_t* this = (full_bv_sat_t*) super;
  bb_sat_solver_destruct(&this->solver);
}

/** Allocate the sub-explainer and setup the methods */
bv_subexplainer_t* full_bv_sat_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {

  full_bv_sat_t* exp = safe_malloc(sizeof(full_bv_sat_t));

  // Construct the supert
  bv_subexplainer_construct(&exp->super, "mcsat::bv::explain::full_bv_sat", ctx, wlm, eval);

  // Setup calls
  exp->super.can_explain_conflict = can_explain_conflict;
  exp->super.explain_conflict = explain_conflict;
  exp->super.can_explain_propagation = can_explain_propagation;
  exp->super.explain_propagation = explain_propagation;
  exp->super.destruct = destruct;

  // Construct the rest
  bb_sat_solver_construct(&exp->solver, ctx, false);

  return (bv_subexplainer_t*) exp;
}

