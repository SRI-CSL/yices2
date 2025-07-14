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

#include "mcsat/tracing.h"
#include "mcsat/na/na_plugin_internal.h"

void na_plugin_get_constraint_variables(na_plugin_t* na, term_t constraint, int_mset_t* vars_out) {

  term_table_t* terms = na->ctx->terms;

  term_t atom = unsigned_term(constraint);
  term_kind_t atom_kind = term_kind(na->ctx->terms, atom);

  switch (atom_kind) {
  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
    na_plugin_get_term_variables(na, arith_atom_arg(terms, atom), vars_out);
    break;
  case EQ_TERM:
  case ARITH_BINEQ_ATOM:
    na_plugin_get_term_variables(na, composite_term_arg(terms, atom, 0), vars_out);
    na_plugin_get_term_variables(na, composite_term_arg(terms, atom, 1), vars_out);
    break;
  case ARITH_ROOT_ATOM:
    na_plugin_get_term_variables(na, arith_root_atom_desc(terms, atom)->p, vars_out);
    break;
  default:
    // We're fine, just a variable, arithmetic term to eval, or a foreign term
    na_plugin_get_term_variables(na, constraint, vars_out);
    int_mset_add(vars_out, variable_db_get_variable(na->ctx->var_db, constraint));
    break;
  }
}

void na_plugin_get_term_variables(na_plugin_t* na, term_t t, int_mset_t* vars_out) {

  // The term table
  term_table_t* terms = na->ctx->terms;

  // Variable database
  variable_db_t* var_db = na->ctx->var_db;


  if (ctx_trace_enabled(na->ctx, "mcsat::new_term")) {
    ctx_trace_printf(na->ctx, "na_plugin_get_variables: ");
    ctx_trace_term(na->ctx, t);
  }

  term_kind_t kind = term_kind(terms, t);
  switch (kind) {
  case ARITH_CONSTANT:
    break;
  case ARITH_POLY: {
    // The polynomial
    polynomial_t* polynomial = poly_term_desc(terms, t);
    // Go through the polynomial and get the variables
    uint32_t i, j, deg;
    variable_t var;
    for (i = 0; i < polynomial->nterms; ++i) {
      term_t product = polynomial->mono[i].var;
      if (product == const_idx) {
        // Just the constant
        continue;
      } else if (term_kind(terms, product) == POWER_PRODUCT) {
        pprod_t* pprod = pprod_for_term(terms, product);
        for (j = 0; j < pprod->len; ++j) {
          var = variable_db_get_variable(var_db, pprod->prod[j].var);
          for (deg = 0; deg < pprod->prod[j].exp; ++ deg) {
            int_mset_add(vars_out, var);
          }
        }
      } else {
        // Variable, or foreign term
        var = variable_db_get_variable(var_db, product);
        int_mset_add(vars_out, var);
      }
    }
    break;
  }
  case POWER_PRODUCT: {
    pprod_t* pprod = pprod_term_desc(terms, t);
    uint32_t i, deg;
    for (i = 0; i < pprod->len; ++ i) {
      variable_t var = variable_db_get_variable(var_db, pprod->prod[i].var);
      for (deg = 0; deg < pprod->prod[i].exp; ++ deg) {
        int_mset_add(vars_out, var);
      }
    }
    break;
  }
  default:
    // A variable or a foreign term
    int_mset_add(vars_out, variable_db_get_variable(var_db, t));
  }
}

void na_plugin_note_conflict(na_plugin_t* na, variable_t variable) {
  if (na->conflict_variable == variable_null) {
    na->conflict_variable = variable;
  }
}

void na_plugin_note_int_conflict(na_plugin_t* na, variable_t variable) {
  if (na->conflict_variable_int == variable_null) {
    na->conflict_variable_int = variable;
  }
}

int na_plugin_is_conflict_pending(na_plugin_t* na) {
  bool conflict_var_set = na->conflict_variable != variable_null || na->conflict_variable_int != variable_null;
  return conflict_var_set && trail_is_consistent(na->ctx->trail);
}

void na_plugin_report_pending_conflict(na_plugin_t* na, trail_token_t* prop) {
  if (!na_plugin_is_conflict_pending(na)) {
    return;
  }

  if (na->conflict_variable != variable_null) {
    na_plugin_report_conflict(na, prop, na->conflict_variable);
  } else if (na->conflict_variable_int != variable_null) {
    na_plugin_report_int_conflict(na, prop, na->conflict_variable_int);
  } else {
    assert(0);
  }
}

void na_plugin_report_conflict(na_plugin_t* na, trail_token_t* prop, variable_t variable) {
  prop->conflict(prop);
  na->conflict_variable = variable;
  (*na->stats.conflicts) ++;
}

void na_plugin_report_int_conflict(na_plugin_t* na, trail_token_t* prop, variable_t variable) {
  prop->conflict(prop);
  na->conflict_variable_int = variable;
  (*na->stats.conflicts_int) ++;
}

void na_plugin_report_assumption_conflict(na_plugin_t* na, trail_token_t* prop, variable_t variable, const mcsat_value_t* value) {
  prop->conflict(prop);
  na->conflict_variable_assumption = variable;
  assert(value->type == VALUE_LIBPOLY);
  lp_value_assign(&na->conflict_variable_value, &value->lp_value);
  (*na->stats.conflicts_assumption) ++;
}
