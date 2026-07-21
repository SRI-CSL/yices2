/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "mcsat/ff/ff_plugin_internal.h"

#include "mcsat/tracing.h"

void ff_plugin_get_constraint_variables(ff_plugin_t* ff, term_t constraint, int_mset_t* vars_out) {

  term_table_t* terms = ff->ctx->terms;

  term_t atom = unsigned_term(constraint);
  term_kind_t atom_kind = term_kind(ff->ctx->terms, atom);

  switch (atom_kind) {
  case ARITH_FF_EQ_ATOM:
    ff_plugin_get_term_variables(ff, arith_ff_eq_arg(terms, atom), vars_out);
    break;
  case EQ_TERM:
  case ARITH_FF_BINEQ_ATOM:
    ff_plugin_get_term_variables(ff, composite_term_arg(terms, atom, 0), vars_out);
    ff_plugin_get_term_variables(ff, composite_term_arg(terms, atom, 1), vars_out);
    break;
  default:
    // We're fine, just a variable, arithmetic term to eval, or a foreign term
    ff_plugin_get_term_variables(ff, constraint, vars_out);
    int_mset_add(vars_out, variable_db_get_variable(ff->ctx->var_db, constraint));
    break;
  }
}

void ff_plugin_get_term_variables(ff_plugin_t* ff, term_t t, int_mset_t* vars_out) {

  // The term table
  term_table_t* terms = ff->ctx->terms;

  // Variable database
  variable_db_t* var_db = ff->ctx->var_db;


  if (ctx_trace_enabled(ff->ctx, "mcsat::new_term")) {
    ctx_trace_printf(ff->ctx, "ff_plugin_get_variables: ");
    ctx_trace_term(ff->ctx, t);
  }

  term_kind_t kind = term_kind(terms, t);
  switch (kind) {
  case ARITH_FF_CONSTANT:
    break;
  case ARITH_FF_POLY: {
    // The polynomial
    polynomial_t* polynomial = finitefield_poly_term_desc(terms, t);
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
