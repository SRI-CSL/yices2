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

#include "ff_libpoly.h"

#include "mcsat/ff/ff_plugin_internal.h"
#include "mcsat/tracing.h"

#include <poly/polynomial.h>
#include <poly/variable_db.h>
#include <poly/feasibility_set.h>
#include <poly/interval.h>
#include <poly/assignment.h>

lp_polynomial_t* lp_polynomial_from_term_ff(ff_plugin_t* ff, term_t t, lp_integer_t* c) {
  if (ctx_trace_enabled(ff->ctx, "ff::terms")) {
    ctx_trace_printf(ff->ctx, "lp_polynomial_from_term: t = ");
    ctx_trace_term(ff->ctx, t);
  }

  lp_polynomial_t* result = lp_polynomial_from_term(&ff->lp_data, t, ff->ctx->terms, c);

  if (ctx_trace_enabled(ff->ctx, "ff::terms")) {
    ctx_trace_printf(ff->ctx, "lp_polynomial_from_term: result = ");
    lp_polynomial_print(result, ctx_trace_out(ff->ctx));
    ctx_trace_printf(ff->ctx, "\n");
  }

  return result;
}

term_t lp_polynomial_to_yices_term_ff(ff_plugin_t *ff, const lp_polynomial_t *lp_p) {
  if (ctx_trace_enabled(ff->ctx, "ff::terms")) {
    ctx_trace_printf(ff->ctx, "lp_polynomial_to_yices_term(");
    lp_polynomial_print(lp_p, ctx_trace_out(ff->ctx));
    ctx_trace_printf(ff->ctx, ")\n");
  }

  term_t result = lp_polynomial_to_yices_term(&ff->lp_data, lp_p, ff->ctx->terms, &ff->buffer);

  if (ctx_trace_enabled(ff->ctx, "ff::terms")) {
    ctx_trace_printf(ff->ctx, "lp_polynomial_to_yices_term(");
    lp_polynomial_print(lp_p, ctx_trace_out(ff->ctx));
    ctx_trace_printf(ff->ctx, ") => [%d] ", result);
    ctx_trace_term(ff->ctx, result);
  }

  return result;
}

void ff_poly_constraint_create(ff_plugin_t *ff, variable_t constraint_var) {
  // assert(poly_constraint_db_check(db));

  if (poly_constraint_db_has(ff->constraint_db, constraint_var)) {
    // Already added
    return;
  }

  term_t t1, t2;
  term_kind_t kind;
  term_t constraint_var_term;

  // Constraint components
  lp_polynomial_t* cstr_polynomial;
  lp_sign_condition_t sgn_condition;

  // Result constraint
  poly_constraint_t* cstr;

  // Context
  variable_db_t* var_db = ff->ctx->var_db;
  term_table_t* terms = ff->ctx->terms;

  // Get the term of the variable
  constraint_var_term = variable_db_get_term(var_db, constraint_var);

  // Depending on the kind, make the constraints
  kind = term_kind(terms, constraint_var_term);
  switch (kind) {
  case ARITH_FF_EQ_ATOM: {
    // p == 0
    t1 = arith_atom_arg(terms, constraint_var_term);
    cstr_polynomial = lp_polynomial_from_term_ff(ff, t1, NULL);
    sgn_condition = LP_SGN_EQ_0;
    break;
  }
  case EQ_TERM:
  case ARITH_BINEQ_ATOM: {
    // LHS = RHS
    t1 = composite_term_arg(terms, constraint_var_term, 0);
    t2 = composite_term_arg(terms, constraint_var_term, 1);
    // Get the polynomials
    lp_integer_t t1_c, t2_c;
    lp_integer_construct(&t1_c);
    lp_integer_construct(&t2_c);
    lp_polynomial_t* t1_p = lp_polynomial_from_term_ff(ff, t1, &t1_c);
    lp_polynomial_t* t2_p = lp_polynomial_from_term_ff(ff, t2, &t2_c);
    //  t1_p/t1_c = t2_p/t2_c
    //  t1_p*t2_c - t2_p*t1_c
    lp_integer_neg(lp_Z, &t1_c, &t1_c);
    lp_polynomial_mul_integer(t1_p, t1_p, &t2_c);
    lp_polynomial_mul_integer(t2_p, t2_p, &t1_c);
    // Add them
    cstr_polynomial = lp_data_new_polynomial(&ff->lp_data);
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
  default: {
    // terms like (x+y), we create regular constraint (x+y) = x + y
    lp_integer_t t1_c, t2_c;
    lp_integer_construct_from_int(lp_Z, &t1_c, 1);
    lp_integer_construct(&t2_c);
    lp_polynomial_t* t1_p = lp_polynomial_alloc();
    term_t t = variable_db_get_term(ff->ctx->var_db, constraint_var);
    lp_variable_t constraint_lp_var = lp_data_get_lp_variable_from_term(&ff->lp_data, t);
    lp_polynomial_construct_simple(t1_p, ff->lp_data.lp_ctx, &t1_c, constraint_lp_var, 1);
    lp_polynomial_t* t2_p = lp_polynomial_from_term_ff(ff, constraint_var_term, &t2_c);
    //  t1_p/t1_c = t2_p/t2_c
    //  t1_p*t2_c - t2_p*t1_c
    lp_integer_neg(lp_Z, &t1_c, &t1_c);
    lp_polynomial_mul_integer(t2_p, t2_p, &t1_c);
    lp_polynomial_mul_integer(t1_p, t1_p, &t2_c);
    // Add them
    cstr_polynomial = lp_data_new_polynomial(&ff->lp_data);
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

  cstr = poly_constraint_new_regular(cstr_polynomial, sgn_condition);
  (*ff->stats.constraint) ++;

  if (ctx_trace_enabled(ff->ctx, "mcsat::new_term")) {
    ctx_trace_printf(ff->ctx, "poly_constraint_add: ");
    poly_constraint_print(cstr, ctx_trace_out(ff->ctx));
    ctx_trace_printf(ff->ctx, "\n");
  }

  poly_constraint_db_add_constraint(ff->constraint_db, constraint_var, cstr);
}
