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
 
#include <poly/variable_db.h>

#include "mcsat/nra/nra_plugin_internal.h"
#include "mcsat/tracing.h"

#include "utils/int_hash_map.h"
#include "libpoly_utils.h"

void nra_plugin_get_constraint_variables(nra_plugin_t* nra, term_t constraint, int_mset_t* vars_out) {

  term_table_t* terms = nra->ctx->terms;

  term_t atom = unsigned_term(constraint);
  term_kind_t atom_kind = term_kind(nra->ctx->terms, atom);

  switch (atom_kind) {
  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
    nra_plugin_get_term_variables(nra, arith_atom_arg(terms, atom), vars_out);
    break;
  case EQ_TERM:
  case ARITH_BINEQ_ATOM:
    nra_plugin_get_term_variables(nra, composite_term_arg(terms, atom, 0), vars_out);
    nra_plugin_get_term_variables(nra, composite_term_arg(terms, atom, 1), vars_out);
    break;
  case ARITH_ROOT_ATOM:
    nra_plugin_get_term_variables(nra, arith_root_atom_desc(terms, atom)->p, vars_out);
    break;
  default:
    // We're fine, just a variable, arithmetic term to eval, or a foreign term
    nra_plugin_get_term_variables(nra, constraint, vars_out);
    int_mset_add(vars_out, variable_db_get_variable(nra->ctx->var_db, constraint));
    break;
  }
}

void nra_plugin_get_term_variables(nra_plugin_t* nra, term_t t, int_mset_t* vars_out) {

  // The term table
  term_table_t* terms = nra->ctx->terms;

  // Variable database
  variable_db_t* var_db = nra->ctx->var_db;


  if (ctx_trace_enabled(nra->ctx, "mcsat::new_term")) {
    ctx_trace_printf(nra->ctx, "nra_plugin_get_variables: ");
    ctx_trace_term(nra->ctx, t);
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

void nra_plugin_set_unit_info(nra_plugin_t* nra, variable_t constraint, variable_t unit_var, constraint_unit_info_t value) {

  int_hmap_pair_t* find = NULL;
  int_hmap_pair_t* unit_find = NULL;

  // Add unit tag
  find = int_hmap_find(&nra->constraint_unit_info, constraint);
  if (find == NULL) {
    // First time, just set
    int_hmap_add(&nra->constraint_unit_info, constraint, value);
  } else {
    assert(find->val != value);
    find->val = value;
  }

  // Add unit variable
  unit_find = int_hmap_find(&nra->constraint_unit_var, constraint);
  if (value == CONSTRAINT_UNIT) {
    if (unit_find == NULL) {
      int_hmap_add(&nra->constraint_unit_var, constraint, unit_var);
    } else {
      unit_find->val = unit_var;
    }
  } else {
    if (unit_find != NULL) {
      unit_find->val = variable_null;
    }
  }
}

bool nra_plugin_has_unit_info(const nra_plugin_t* nra, variable_t constraint) {
  int_hmap_pair_t* find = int_hmap_find(&((nra_plugin_t*)nra)->constraint_unit_info, constraint);
  return find != NULL;
}

constraint_unit_info_t nra_plugin_get_unit_info(nra_plugin_t* nra, variable_t constraint) {
  int_hmap_pair_t* find = int_hmap_find(&nra->constraint_unit_info, constraint);
  if (find == NULL)  {
    return CONSTRAINT_UNKNOWN;
  } else {
    return find->val;
  }
}

variable_t nra_plugin_get_unit_var(nra_plugin_t* nra, variable_t constraint) {
  int_hmap_pair_t* find = int_hmap_find(&nra->constraint_unit_var, constraint);
  if (find == NULL) {
    return variable_null;
  } else {
    return find->val;
  }
}

int nra_plugin_term_has_lp_variable(nra_plugin_t* nra, term_t t) {
  variable_t mcsat_var = variable_db_get_variable(nra->ctx->var_db, t);
  int_hmap_pair_t* find = int_hmap_find(&nra->lp_data.mcsat_to_lp_var_map, mcsat_var);
  return find != NULL;
}

int nra_plugin_variable_has_lp_variable(nra_plugin_t* nra, variable_t mcsat_var) {
  int_hmap_pair_t* find = int_hmap_find(&nra->lp_data.mcsat_to_lp_var_map, mcsat_var);
  return find != NULL;
}

void nra_plugin_add_lp_variable_from_term(nra_plugin_t* nra, term_t t) {

  lp_variable_t lp_var = lp_variable_from_term(t, nra->ctx->terms, nra->lp_data.lp_var_db);
  variable_t mcsat_var = variable_db_get_variable(nra->ctx->var_db, t);

  assert(int_hmap_find(&nra->lp_data.lp_to_mcsat_var_map, lp_var) == NULL);
  assert(int_hmap_find(&nra->lp_data.mcsat_to_lp_var_map, mcsat_var) == NULL);

  int_hmap_add(&nra->lp_data.lp_to_mcsat_var_map, lp_var, mcsat_var);
  int_hmap_add(&nra->lp_data.mcsat_to_lp_var_map, mcsat_var, lp_var);
}

void nra_plugin_add_lp_variable(nra_plugin_t* nra, variable_t mcsat_var) {

  term_t t = variable_db_get_term(nra->ctx->var_db, mcsat_var);

  // Name of the term
  char buffer[100];
  char* var_name = term_name(nra->ctx->terms, t);
  if (var_name == NULL) {
    var_name = buffer;
    sprintf(var_name, "#%d", t);
    if (ctx_trace_enabled(nra->ctx, "nra::vars")) {
      ctx_trace_printf(nra->ctx, "%s -> ", var_name);
      variable_db_print_variable(nra->ctx->var_db, mcsat_var, ctx_trace_out(nra->ctx));
      ctx_trace_printf(nra->ctx, "\n");
    }
  }

  // Make the variable
  lp_variable_t lp_var = lp_variable_db_new_variable(nra->lp_data.lp_var_db, var_name);

  assert(int_hmap_find(&nra->lp_data.lp_to_mcsat_var_map, lp_var) == NULL);
  assert(int_hmap_find(&nra->lp_data.mcsat_to_lp_var_map, mcsat_var) == NULL);

  int_hmap_add(&nra->lp_data.lp_to_mcsat_var_map, lp_var, mcsat_var);
  int_hmap_add(&nra->lp_data.mcsat_to_lp_var_map, mcsat_var, lp_var);
}

lp_variable_t nra_plugin_get_lp_variable(nra_plugin_t* nra, variable_t mcsat_var) {
  int_hmap_pair_t* find = int_hmap_find(&nra->lp_data.mcsat_to_lp_var_map, mcsat_var);
  assert(find != NULL);
  return find->val;
}

variable_t nra_plugin_get_variable_from_lp_variable(nra_plugin_t* nra, lp_variable_t lp_var) {
  int_hmap_pair_t* find = int_hmap_find(&nra->lp_data.lp_to_mcsat_var_map, lp_var);
  assert(find != NULL);
  return find->val;
}

void nra_plugin_report_conflict(nra_plugin_t* nra, trail_token_t* prop, variable_t variable) {
  prop->conflict(prop);
  nra->conflict_variable = variable;
  (*nra->stats.conflicts) ++;
}

void nra_plugin_report_int_conflict(nra_plugin_t* nra, trail_token_t* prop, variable_t variable) {
  prop->conflict(prop);
  nra->conflict_variable_int = variable;
  (*nra->stats.conflicts_int) ++;
}

void nra_plugin_report_assumption_conflict(nra_plugin_t* nra, trail_token_t* prop, variable_t variable, const mcsat_value_t* value) {
  prop->conflict(prop);
  nra->conflict_variable_assumption = variable;
  assert(value->type == VALUE_LIBPOLY);
  lp_value_assign(&nra->conflict_variable_value, &value->lp_value);
  (*nra->stats.conflicts_assumption) ++;
}
