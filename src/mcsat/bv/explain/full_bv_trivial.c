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

#include "full_bv_sat.h"

#include "mcsat/tracing.h"
#include "mcsat/value.h"
#include "mcsat/bv/bv_utils.h"
#include "mcsat/mcsat_types.h"
#include "mcsat/variable_db.h"
#include "mcsat/utils/substitution.h"

#include "utils/int_vectors.h"
#include "utils/int_array_sort2.h"

#include "context/context_types.h"

#include "terms/term_manager.h"

#include "yices.h"

#include <inttypes.h>

static
bool can_explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict, variable_t conflict_var) {
  // We can explain anything
  return true;
}

static
void explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict) {
  uint32_t i;
  variable_t atom_i_var;
  term_t atom_i_term;
  bool atom_i_value;

  const variable_db_t* var_db = this->ctx->var_db;
  term_manager_t* tm = this->ctx->tm;
  const mcsat_trail_t* trail = this->ctx->trail;

  // Simple conflict resolution: get the variables and say x != v
  int_mset_t assigned_vars;
  int_mset_construct(&assigned_vars, 0);
  for (i = 0; i < conflict_core->size; ++ i) {
    atom_i_var = conflict_core->data[i];
    atom_i_term = variable_db_get_term(var_db, atom_i_var);
    atom_i_value = trail_get_boolean_value(trail, atom_i_var);
    // Add atom to conflict
    if (atom_i_value) {
      ivector_push(conflict, atom_i_term);
    } else {
      ivector_push(conflict, opposite_term(atom_i_term));
    }
    // Add subvariables to set
    variable_list_ref_t list_ref = watch_list_manager_get_list_of(this->wlm, atom_i_var);
    variable_t* atom_i_vars = watch_list_manager_get_list(this->wlm, list_ref);
    for (; *atom_i_vars != variable_null; atom_i_vars ++) {
      if (*atom_i_vars != atom_i_var) {
        assert(*atom_i_vars == conflict_var || trail_has_value(trail, *atom_i_vars));
        if (*atom_i_vars != conflict_var) {
          int_mset_add(&assigned_vars, *atom_i_vars);
        }
      }
    }
  }

  const ivector_t* assigned_vars_vec = int_mset_get_list(&assigned_vars);
  for (i = 0; i < assigned_vars_vec->size; ++i) {
    variable_t var = assigned_vars_vec->data[i];
    term_t var_term = variable_db_get_term(var_db, var);
    if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
      ctx_trace_printf(this->ctx, "vars:\n");
      ctx_trace_printf(this->ctx, "[%"PRIu32"]: ", i);
      ctx_trace_term(this->ctx, var_term);
    }
    const mcsat_value_t* value = trail_get_value(trail, var);
    if (value->type == VALUE_BOOLEAN) {
      if (value->b) {
        ivector_push(conflict, var_term);
      } else {
        ivector_push(conflict, opposite_term(var_term));
      }
    } else if (value->type == VALUE_BV) {
      term_t var_value = mk_bv_constant(tm, (bvconstant_t*) &value->bv_value);
      term_t var_eq_value = mk_eq(tm, var_term, var_value);
      ivector_push(conflict, var_eq_value);
    } else {
      assert(false);
    }
  }

  int_mset_destruct(&assigned_vars);
}

static
bool can_explain_propagation(bv_subexplainer_t* this, const ivector_t* reasons, variable_t x) {
  return false;
}

static
term_t explain_propagation(bv_subexplainer_t* this, const ivector_t* reasons_in, variable_t x, ivector_t* reasons_out) {
  assert(false);
  return NULL_TERM;
}


/** Allocate the sub-explainer and setup the methods */
bv_subexplainer_t* full_bv_trivial_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {

  bv_subexplainer_t* exp = safe_malloc(sizeof(bv_subexplainer_t));

  // Construct the supert
  bv_subexplainer_construct(exp, "mcsat::bv::explain::full_bv_trivial", ctx, wlm, eval);

  // Setup calls
  exp->can_explain_conflict = can_explain_conflict;
  exp->explain_conflict = explain_conflict;
  exp->can_explain_propagation = can_explain_propagation;
  exp->explain_propagation = explain_propagation;

  return exp;
}

