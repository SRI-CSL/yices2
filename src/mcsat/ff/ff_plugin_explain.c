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
#include <poly/polynomial_hash_set.h>

#include "mcsat/ff/ff_plugin_explain.h"
#include "mcsat/ff/ff_plugin_internal.h"

#include "mcsat/tracing.h"

static inline
term_t lp_projection_map_polynomial_to_term(ff_plugin_t* ff, const lp_polynomial_t* p) {
  return lp_polynomial_to_yices_term(ff->lp_data, p, ff->ctx->tm->terms, &ff->buffer);
}

void ff_plugin_explain_conflict(ff_plugin_t* ff, const ivector_t* core, const ivector_t* lemma_reasons, ivector_t* conflict) {
  const mcsat_trail_t* trail = ff->ctx->trail;
  variable_db_t* var_db = ff->ctx->var_db;

  // TODO check if gcd_simplify_zero works

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

  // TODO implement me

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
}


void ff_plugin_check_conflict(ff_plugin_t* ff, ivector_t* core) {
  // TODO implement me
}
