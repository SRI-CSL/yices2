/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "bv_core_solver.h"

#include "mcsat/plugin.h"
#include "mcsat/tracing.h"

#include "yices.h"

void bv_core_solver_construct(bv_core_solver_t* solver, plugin_context_t* ctx, bool incremental) {
  substitution_construct(&solver->subst, &ctx->var_db->tm, ctx->tracer);
  init_ivector(&solver->vars_to_assign, 0);
  solver->ctx = ctx;
  solver->incremental = incremental;

  // Create an instance of Yices
  solver->config = yices_new_config();
  int32_t ret = yices_default_config_for_logic(solver->config, "QF_BV");
  (void) ret;
  assert(ret == 0);
  solver->yices_ctx = yices_new_context(solver->config);
  assert (solver->yices_ctx != NULL);

  // Incremental, do a push
  if (incremental) {
    yices_push(solver->yices_ctx);
  }
}

void bv_core_solver_destruct(bv_core_solver_t* solver) {
  substitution_destruct(&solver->subst);
  delete_ivector(&solver->vars_to_assign);

  // Delete the yices instance
  yices_free_context(solver->yices_ctx);
  yices_free_config(solver->config);
}

void bv_core_solver_reset(bv_core_solver_t* solver) {
  if (solver->incremental) {
    yices_pop(solver->yices_ctx);
    yices_push(solver->yices_ctx);
    substitution_destruct(&solver->subst);
    substitution_construct(&solver->subst, &solver->ctx->var_db->tm, solver->ctx->tracer);
    ivector_reset(&solver->vars_to_assign);
  } else {
    bv_core_solver_destruct(solver);
    bv_core_solver_construct(solver, solver->ctx, false);
  }
}


void bv_core_solver_add_variable(bv_core_solver_t* solver, variable_t var, bool with_value) {
  // Add new variable to substitute
  term_t var_term = variable_db_get_term(solver->ctx->var_db, var);
  if (!substitution_has_term(&solver->subst, var_term)) {
    if (ctx_trace_enabled(solver->ctx, "mcsat::bv::conflict")) {
      FILE* out = ctx_trace_out(solver->ctx);
      fprintf(out, "Variable: ");
      ctx_trace_term(solver->ctx, var_term);
    }
    // Make a fresh variable if not already a variable
    term_t var_fresh;
    term_kind_t kind = term_kind(solver->yices_ctx->terms, var_term);
    if (kind != UNINTERPRETED_TERM) {
      type_t var_type = yices_type_of_term(var_term);
      var_fresh = yices_new_uninterpreted_term(var_type);
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

void bv_core_solver_assert_term(bv_core_solver_t* solver, variable_t assertion_term) {
  assertion_term = substitution_run_fwd(&solver->subst, assertion_term, 0);
  if (ctx_trace_enabled(solver->ctx, "mcsat::bv::conflict")) {
    FILE* out = trace_out(solver->yices_ctx->trace);
    ctx_trace_term(solver->ctx, assertion_term);
    fprintf(out, "  previously \n");
    ctx_trace_term(solver->ctx, assertion_term);
  }
  yices_assert_formula(solver->yices_ctx, assertion_term);
}

/**
 * Run the substitution and assert (with the same polarity as in MCSAT)
 */
void bv_core_solver_assert_var(bv_core_solver_t* solver, variable_t var) {
  term_t assertion_term = variable_db_get_term(solver->ctx->var_db, var);
  const mcsat_value_t* var_value = trail_get_value(solver->ctx->trail, var);
  assert(var_value->type == VALUE_BOOLEAN);
  if (!var_value->b) {
    assertion_term = opposite_term(assertion_term);
  }
  bv_core_solver_assert_term(solver, assertion_term);
}

bool bv_solver_cmp_var_by_trail_index(void *data, variable_t t1, variable_t t2) {
  const mcsat_trail_t* trail = data;
  assert(trail_has_value(trail, t1));
  assert(trail_has_value(trail, t2));
  return trail_get_index(trail, t1) < trail_get_index(trail, t2);
}

void bv_core_solver_solve_and_get_core(bv_core_solver_t* solver, term_vector_t* core) {

  plugin_context_t* ctx = solver->ctx;
  const variable_db_t* var_db = ctx->var_db;
  const mcsat_trail_t* trail = ctx->trail;
  term_manager_t* tm = &solver->ctx->var_db->tm;

  // Vector to store assumptions
  ivector_t assumptions;
  init_ivector(&assumptions, 0);

  // Sort variables to assign according to their trail index
  // int_array_sort2(solver->vars_to_assign.data, solver->vars_to_assign.size, (void*) solver->ctx->trail, bv_solver_cmp_var_by_trail_index);

  // Make assumptions
  uint32_t i, bit;
  for (i = 0; i < solver->vars_to_assign.size; ++ i) {
    // Variable and its value
    variable_t var = solver->vars_to_assign.data[i];
    const mcsat_value_t* var_value = trail_get_value(trail, var);
    assert(var_value->type == VALUE_BOOLEAN || var_value->type == VALUE_BV);
    // Get the term, and it's substitution
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
  smt_status_t status = yices_check_context_with_assumptions(solver->yices_ctx, NULL, assumptions.size, assumptions.data);
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

  if (ctx_trace_enabled(ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Core: \n");
    for (i = 0; i < core->size; ++ i) {
      ctx_trace_term(ctx, core->data[i]);
    }
  }

  // Remove assumption vector
  delete_ivector(&assumptions);
}
