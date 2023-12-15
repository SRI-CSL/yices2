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

#include "nra_libpoly.h"

#include "mcsat/nra/nra_plugin_internal.h"
#include "mcsat/utils/lp_utils.h"
#include "mcsat/tracing.h"

#include <poly/polynomial.h>
#include <poly/variable_db.h>
#include <poly/feasibility_set.h>
#include <poly/interval.h>
#include <poly/assignment.h>

lp_polynomial_t* lp_polynomial_from_term_nra(nra_plugin_t* nra, term_t t, lp_integer_t* c) {
  if (ctx_trace_enabled(nra->ctx, "nra::terms")) {
    ctx_trace_printf(nra->ctx, "lp_polynomial_from_term: t = ");
    ctx_trace_term(nra->ctx, t);
  }

  lp_polynomial_t* result = lp_polynomial_from_term(&nra->lp_data, t, nra->ctx->terms, c);

  if (ctx_trace_enabled(nra->ctx, "nra::terms")) {
    ctx_trace_printf(nra->ctx, "lp_polynomial_from_term: result = ");
    lp_polynomial_print(result, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, "\n");
  }

  return result;
}

term_t lp_polynomial_to_yices_term_nra(nra_plugin_t *nra, const lp_polynomial_t *lp_p) {
  if (ctx_trace_enabled(nra->ctx, "nra::terms")) {
    ctx_trace_printf(nra->ctx, "lp_polynomial_to_yices_term(");
    lp_polynomial_print(lp_p, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, ")\n");
  }

  term_t result = lp_polynomial_to_yices_term(&nra->lp_data, lp_p, nra->ctx->terms, &nra->buffer);

  if (ctx_trace_enabled(nra->ctx, "nra::terms")) {
    ctx_trace_printf(nra->ctx, "lp_polynomial_to_yices_term(");
    lp_polynomial_print(lp_p, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, ") => [%d] ", result);
    ctx_trace_term(nra->ctx, result);
  }

  return result;
}

void nra_poly_constraint_create(nra_plugin_t *nra, variable_t constraint_var) {
  // assert(poly_constraint_db_check(db));

  if (poly_constraint_db_has(nra->constraint_db, constraint_var)) {
    // Already added
    return;
  }

  term_t t1, t2;
  term_kind_t kind;
  term_t constraint_var_term;

  // Constraint components
  lp_polynomial_t* cstr_polynomial;
  lp_variable_t cstr_root_variable = lp_variable_null;
  uint32_t cstr_root_index;
  lp_sign_condition_t sgn_condition;

  // Result constraint
  poly_constraint_t* cstr;

  // Context
  variable_db_t* var_db = nra->ctx->var_db;
  term_table_t* terms = nra->ctx->terms;

  // Get the term of the variable
  constraint_var_term = variable_db_get_term(var_db, constraint_var);

  // Depending on the kind, make the constraints
  kind = term_kind(terms, constraint_var_term);
  switch (kind) {
  case ARITH_EQ_ATOM: {
    // p == 0
    t1 = arith_atom_arg(terms, constraint_var_term);
    cstr_polynomial = lp_polynomial_from_term_nra(nra, t1, NULL);
    sgn_condition = LP_SGN_EQ_0;
    break;
  }
  case ARITH_GE_ATOM:
    // p >= 0
    t1 = arith_atom_arg(terms, constraint_var_term);
    cstr_polynomial = lp_polynomial_from_term_nra(nra, t1, NULL);
    sgn_condition = LP_SGN_GE_0;
    break;
  case EQ_TERM:
  case ARITH_BINEQ_ATOM: {
    // LHS = RHS
    t1 = composite_term_arg(terms, constraint_var_term, 0);
    t2 = composite_term_arg(terms, constraint_var_term, 1);
    // Get the polynomials
    lp_integer_t t1_c, t2_c;
    lp_integer_construct(&t1_c);
    lp_integer_construct(&t2_c);
    lp_polynomial_t* t1_p = lp_polynomial_from_term_nra(nra, t1, &t1_c);
    lp_polynomial_t* t2_p = lp_polynomial_from_term_nra(nra, t2, &t2_c);
    //  t1_p/t1_c = t2_p/t2_c
    //  t1_p*t2_c - t2_p*t1_c
    lp_integer_neg(lp_Z, &t1_c, &t1_c);
    lp_polynomial_mul_integer(t1_p, t1_p, &t2_c);
    lp_polynomial_mul_integer(t2_p, t2_p, &t1_c);
    // Add them
    cstr_polynomial = lp_data_new_polynomial(&nra->lp_data);
    lp_polynomial_add(cstr_polynomial, t1_p, t2_p);
    // p1 = p2
    sgn_condition = LP_SGN_EQ_0;
    // Remove temps
    lp_polynomial_delete(t1_p);
    lp_polynomial_delete(t2_p);
    lp_integer_destruct(&t1_c);
    lp_integer_destruct(&t2_c);
    break;
  }
  case ARITH_ROOT_ATOM: {
    root_atom_t* r = arith_root_atom_desc(terms, constraint_var_term);
    cstr_polynomial = lp_polynomial_from_term_nra(nra, r->p, NULL);
    assert(variable_db_has_variable(nra->ctx->var_db, r->x));
    cstr_root_variable = lp_data_get_lp_variable_from_term(&nra->lp_data, r->x);
    cstr_root_index = r->k;
    switch (r->r) {
    case ROOT_ATOM_LT:
      sgn_condition = LP_SGN_LT_0;
      break;
    case ROOT_ATOM_LEQ:
      sgn_condition = LP_SGN_LE_0;
      break;
    case ROOT_ATOM_EQ:
      sgn_condition = LP_SGN_EQ_0;
      break;
    case ROOT_ATOM_NEQ:
      sgn_condition = LP_SGN_NE_0;
      break;
    case ROOT_ATOM_GEQ:
      sgn_condition = LP_SGN_GE_0;
      break;
    case ROOT_ATOM_GT:
      sgn_condition = LP_SGN_GT_0;
      break;
    default:
      sgn_condition = LP_SGN_EQ_0;
      assert(false);
      break;
    }
    break;
  }
  default: {
    // terms like (x+y), we create regular constraint (x+y) = x + y
    lp_integer_t t1_c, t2_c;
    lp_integer_construct_from_int(lp_Z, &t1_c, 1);
    lp_integer_construct(&t2_c);
    lp_polynomial_t* t1_p = lp_polynomial_alloc();
    term_t t = variable_db_get_term(nra->ctx->var_db, constraint_var);
    lp_variable_t constraint_lp_var = lp_data_get_lp_variable_from_term(&nra->lp_data, t);
    lp_polynomial_construct_simple(t1_p, nra->lp_data.lp_ctx, &t1_c, constraint_lp_var, 1);
    lp_polynomial_t* t2_p = lp_polynomial_from_term_nra(nra, constraint_var_term, &t2_c);
    //  t1_p/t1_c = t2_p/t2_c
    //  t1_p*t2_c - t2_p*t1_c
    lp_integer_neg(lp_Z, &t1_c, &t1_c);
    lp_polynomial_mul_integer(t2_p, t2_p, &t1_c);
    lp_polynomial_mul_integer(t1_p, t1_p, &t2_c);
    // Add them
    cstr_polynomial = lp_data_new_polynomial(&nra->lp_data);
    lp_polynomial_add(cstr_polynomial, t1_p, t2_p);
    // p1 = p2
    sgn_condition = LP_SGN_EQ_0;
    // Remove temps
    lp_polynomial_delete(t1_p);
    lp_polynomial_delete(t2_p);
    lp_integer_destruct(&t1_c);
    lp_integer_destruct(&t2_c);

    break;
  }
  }

  // Create the appropriate constraint
  if (cstr_root_variable == lp_variable_null) {
    cstr = poly_constraint_new_regular(cstr_polynomial, sgn_condition);
    (*nra->stats.constraint_regular) ++;
  } else {
    cstr = poly_constraint_new_root(cstr_polynomial, sgn_condition, cstr_root_variable, cstr_root_index);
    (*nra->stats.constraint_root) ++;
  }

  if (ctx_trace_enabled(nra->ctx, "mcsat::new_term")) {
    ctx_trace_printf(nra->ctx, "poly_constraint_add: ");
    poly_constraint_print(cstr, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, "\n");
  }

  poly_constraint_db_add_constraint(nra->constraint_db, constraint_var, cstr);
}

const mcsat_value_t* nra_poly_constraint_db_approximate(nra_plugin_t* nra, variable_t constraint_var) {
  poly_constraint_db_t* db = nra->constraint_db;
  const mcsat_value_t* result = NULL;

  // Get the constraints
  const poly_constraint_t* cstr = poly_constraint_db_get(db, constraint_var);
  if (poly_constraint_is_root_constraint(cstr)) {
    // TODO: check if possible
    return NULL;
  }

  // Reset the interval assignment
  lp_interval_assignment_t* m = nra->lp_data.lp_interval_assignment;
  lp_interval_assignment_reset(m);

  // Set up the assignment x -> I(x)
  assert(watch_list_manager_has_constraint(&nra->wlm, constraint_var));
  variable_list_ref_t var_list_ref = watch_list_manager_get_list_of(&nra->wlm, constraint_var);
  variable_t* vars = watch_list_manager_get_list(&nra->wlm, var_list_ref);
  for (; *vars != variable_null; vars++) {
    variable_t x = *vars;
    term_t t = variable_db_get_term(nra->ctx->var_db, x);
    lp_variable_t x_lp = lp_data_get_lp_variable_from_term(&nra->lp_data, t);
    lp_interval_t x_interval;
    lp_interval_construct_full(&x_interval);
    feasible_set_db_approximate_value(nra->feasible_set_db, x, &x_interval);
    if (ctx_trace_enabled(nra->ctx, "mcsat::nra::learn")) {
      ctx_trace_printf(nra->ctx, " ");
      ctx_trace_term(nra->ctx, variable_db_get_term(nra->ctx->var_db, x));
      ctx_trace_printf(nra->ctx, " ");
      lp_interval_print(&x_interval, ctx_trace_out(nra->ctx));
      ctx_trace_printf(nra->ctx, "\n");
    }
    lp_interval_assignment_set_interval(m, x_lp, &x_interval);
    lp_interval_destruct(&x_interval);
  }

  // Evaluate the polynomial
  lp_interval_t value;
  lp_interval_construct_full(&value);
  lp_polynomial_interval_value(cstr->polynomial, m, &value);
  if (ctx_trace_enabled(nra->ctx, "mcsat::nra::learn")) {
    poly_constraint_print(cstr, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, " -> ");
    lp_interval_print(&value, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, "\n");
  }

  lp_sign_condition_t pos = cstr->sgn_condition;
  lp_sign_condition_t neg = lp_sign_condition_negate(cstr->sgn_condition);

  if (lp_sign_condition_consistent_interval(pos, &value)) {
    result = &mcsat_value_true;
  } else if (lp_sign_condition_consistent_interval(neg, &value)) {
    result = &mcsat_value_false;
  }

  // Remove temps
  lp_interval_destruct(&value);

  return result;
}
