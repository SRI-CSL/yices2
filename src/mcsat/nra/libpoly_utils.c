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
 
#include "mcsat/nra/libpoly_utils.h"
#include "mcsat/nra/nra_plugin_internal.h"
#include "mcsat/tracing.h"

#include "terms/balanced_arith_buffers.h"
#include "terms/rba_buffer_terms.h"
#include "terms/term_manager.h"

#include <poly/monomial.h>

#include <gmp.h>

lp_polynomial_t* lp_polynomial_from_power_product_nra(nra_plugin_t* nra, pprod_t* pp, lp_integer_t* c) {

  // Context
  lp_polynomial_context_t* lp_ctx = nra->lp_data.lp_ctx;

  // The monomials
  lp_monomial_t lp_monomial;
  lp_monomial_construct(lp_ctx, &lp_monomial);

  // Set monomial coefficient to 1
  lp_integer_t one;
  lp_integer_construct_from_int(lp_Z, &one, 1);
  lp_monomial_set_coefficient(lp_ctx, &lp_monomial, &one);
  lp_integer_destruct(&one);

  // Get the product terms
  uint32_t i = 0;
  for (i = 0; i < pp->len; ++ i) {
    variable_t var = variable_db_get_variable(nra->ctx->var_db, pp->prod[i].var);
    lp_variable_t lp_var = nra_plugin_get_lp_variable(nra, var);
    lp_monomial_push(&lp_monomial, lp_var, pp->prod[i].exp);
  }

  lp_polynomial_t* result = lp_polynomial_new(nra->lp_data.lp_ctx);
  lp_polynomial_add_monomial(result, &lp_monomial);

  if (c) {
    lp_integer_assign_int(lp_Z, c, 1);
  }

  lp_monomial_destruct(&lp_monomial);

  return result;
}

lp_polynomial_t* lp_polynomial_from_power_product(pprod_t* pp, int_hmap_t* term_to_lp_map, const lp_polynomial_context_t* lp_ctx, lp_integer_t* c) {

  // The monomials
  lp_monomial_t lp_monomial;
  lp_monomial_construct(lp_ctx, &lp_monomial);

  // Set monomial coefficient to 1
  lp_integer_t one;
  lp_integer_construct_from_int(lp_Z, &one, 1);
  lp_monomial_set_coefficient(lp_ctx, &lp_monomial, &one);
  lp_integer_destruct(&one);

  // Get the product terms
  uint32_t i = 0;
  for (i = 0; i < pp->len; ++ i) {
    int_hmap_pair_t* var_find = int_hmap_find(term_to_lp_map, pp->prod[i].var);
    assert(var_find != NULL);
    lp_variable_t lp_var = var_find->val;
    lp_monomial_push(&lp_monomial, lp_var, pp->prod[i].exp);
  }

  lp_polynomial_t* result = lp_polynomial_new(lp_ctx);
  lp_polynomial_add_monomial(result, &lp_monomial);

  if (c) {
    lp_integer_assign_int(lp_Z, c, 1);
  }

  lp_monomial_destruct(&lp_monomial);

  return result;
}

lp_polynomial_t* lp_polynomial_from_polynomial_nra(nra_plugin_t* nra, polynomial_t* p, lp_integer_t* c) {

  uint32_t i, j;
  variable_t var;
  lp_variable_t lp_var;

  lp_polynomial_t* result = lp_polynomial_new(nra->lp_data.lp_ctx);

  //
  // we have
  // q_1 + q_2*p_2 + ... + q_n p_n
  //
  // with q rationals, and p power products
  //
  // we get the lcm of the denominators first, and multiply it out
  //

  // Integers to represent rationals
  lp_integer_t a, b;
  lp_integer_construct(&a);
  lp_integer_construct(&b);

  // Compute the lcm
  lp_integer_t lcm;
  lp_integer_construct_from_int(lp_Z, &lcm, 1);
  for (i = 0; i < p->nterms; ++ i) {
    lp_integer_assign_yices_rational(&a, &b, &p->mono[i].coeff);
    lp_integer_lcm_Z(&lcm, &lcm, &b);
  }

  // Assign to c
  if (c) {
    lp_integer_assign(lp_Z, c, &lcm);
  }

  // Context
  term_table_t* terms = nra->ctx->terms;
  variable_db_t* var_db = nra->ctx->var_db;
  lp_polynomial_context_t* lp_ctx = nra->lp_data.lp_ctx;

  // The monomials
  lp_monomial_t lp_monomial;
  lp_monomial_construct(lp_ctx, &lp_monomial);

  // Add up all the monomials
  for (i = 0; i < p->nterms; ++ i) {

    term_t product = p->mono[i].var;
    lp_monomial_clear(lp_ctx, &lp_monomial);

    // The constant (a/b)*lcm
    lp_integer_assign_yices_rational(&a, &b, &p->mono[i].coeff);
    lp_integer_div_exact(lp_Z, &b, &lcm, &b);
    lp_integer_mul(lp_Z, &a, &a, &b);
    lp_monomial_set_coefficient(lp_ctx, &lp_monomial, &a);

    if (product == const_idx) {
      // Constant polynomial, nothing to do
    } else if (term_kind(terms, product) == POWER_PRODUCT) {
      // Add all the variables
      pprod_t* pprod = pprod_for_term(terms, product);
      for (j = 0; j < pprod->len; ++j) {
        var = variable_db_get_variable(var_db, pprod->prod[j].var);
        lp_var = nra_plugin_get_lp_variable(nra, var);
        lp_monomial_push(&lp_monomial, lp_var, pprod->prod[j].exp);
      }
    } else {
      // Variable, or foreign term
      var = variable_db_get_variable(var_db, product);
      lp_var = nra_plugin_get_lp_variable(nra, var);
      lp_monomial_push(&lp_monomial, lp_var, 1);
    }

    // Add the monomial to the polynomial
    lp_polynomial_add_monomial(result, &lp_monomial);
  }

  // Remove temps
  lp_monomial_destruct(&lp_monomial);
  lp_integer_destruct(&a);
  lp_integer_destruct(&b);
  lp_integer_destruct(&lcm);

  return result;
}

lp_polynomial_t* lp_polynomial_from_polynomial(polynomial_t* p, term_table_t* terms, int_hmap_t* term_to_lp_map, const lp_polynomial_context_t* lp_ctx, lp_integer_t* c) {

  uint32_t i, j;
  lp_variable_t lp_var;

  lp_polynomial_t* result = lp_polynomial_new(lp_ctx);

  //
  // we have
  // q_1 + q_2*p_2 + ... + q_n p_n
  //
  // with q rationals, and p power products
  //
  // we get the lcm of the denominators first, and multiply it out
  //

  // Integers to represent rationals
  lp_integer_t a, b;
  lp_integer_construct(&a);
  lp_integer_construct(&b);

  // Compute the lcm
  lp_integer_t lcm;
  lp_integer_construct_from_int(lp_Z, &lcm, 1);
  for (i = 0; i < p->nterms; ++ i) {
    lp_integer_assign_yices_rational(&a, &b, &p->mono[i].coeff);
    lp_integer_lcm_Z(&lcm, &lcm, &b);
  }

  // Assign to c
  if (c) {
    lp_integer_assign(lp_Z, c, &lcm);
  }

  // The monomials
  lp_monomial_t lp_monomial;
  lp_monomial_construct(lp_ctx, &lp_monomial);

  // Add up all the monomials
  for (i = 0; i < p->nterms; ++ i) {

    term_t product = p->mono[i].var;
    lp_monomial_clear(lp_ctx, &lp_monomial);

    // The constant (a/b)*lcm
    lp_integer_assign_yices_rational(&a, &b, &p->mono[i].coeff);
    lp_integer_div_exact(lp_Z, &b, &lcm, &b);
    lp_integer_mul(lp_Z, &a, &a, &b);
    lp_monomial_set_coefficient(lp_ctx, &lp_monomial, &a);

    if (product == const_idx) {
      // Constant polynomial, nothing to do
    } else if (term_kind(terms, product) == POWER_PRODUCT) {
      // Add all the variables
      pprod_t* pprod = pprod_for_term(terms, product);
      for (j = 0; j < pprod->len; ++j) {
        int_hmap_pair_t* var_find = int_hmap_find(term_to_lp_map, pprod->prod[j].var);
        assert(var_find != NULL);
        lp_var = var_find->val;
        lp_monomial_push(&lp_monomial, lp_var, pprod->prod[j].exp);
      }
    } else {
      // Variable, or foreign term
      int_hmap_pair_t* var_find = int_hmap_find(term_to_lp_map, product);
      assert(var_find != NULL);
      lp_var = var_find->val;
      lp_monomial_push(&lp_monomial, lp_var, 1);
    }

    // Add the monomial to the polynomial
    lp_polynomial_add_monomial(result, &lp_monomial);
  }

  // Remove temps
  lp_monomial_destruct(&lp_monomial);
  lp_integer_destruct(&a);
  lp_integer_destruct(&b);
  lp_integer_destruct(&lcm);

  return result;
}
lp_polynomial_t* lp_polynomial_from_term_nra(nra_plugin_t* nra, term_t t, lp_integer_t* c) {
  term_kind_t kind;
  lp_polynomial_t* result = NULL;
  term_table_t* terms = nra->ctx->terms;

  if (ctx_trace_enabled(nra->ctx, "nra::terms")) {
    ctx_trace_printf(nra->ctx, "lp_polynomial_from_term: t = ");
    ctx_trace_term(nra->ctx, t);
  }

  kind = term_kind(terms, t);
  switch (kind) {
  case ARITH_POLY:
    result = lp_polynomial_from_polynomial_nra(nra, poly_term_desc(terms, t), c);
    break;
  case ARITH_CONSTANT: {
    // Get the constant numerator and denominator
    lp_integer_t lp_p;
    lp_integer_construct_from_int(lp_Z, &lp_p, 0);
    lp_integer_assign_yices_rational(&lp_p, c, rational_term_desc(terms, t));
    // polynomial a*x^0
    result = lp_polynomial_alloc();
    lp_polynomial_construct_simple(result, nra->lp_data.lp_ctx, &lp_p, 0, 0);
    // Remove temp
    lp_integer_destruct(&lp_p);
    break;
  }
  case POWER_PRODUCT:
    result = lp_polynomial_from_power_product_nra(nra, pprod_term_desc(terms, t), c);
    break;
  default: {
    // Constant 1
    lp_integer_t one;
    lp_integer_construct_from_int(lp_Z, &one, 1);
    // The variable
    variable_t t_var = variable_db_get_variable_if_exists(nra->ctx->var_db, t);
    lp_variable_t lp_var = nra_plugin_get_lp_variable(nra, t_var);
    // Polynomial 1*x^1
    result = lp_polynomial_alloc();
    lp_polynomial_construct_simple(result, nra->lp_data.lp_ctx, &one, lp_var, 1);
    // Put 1 if requested
    if (c != NULL) {
      lp_integer_assign(lp_Z, c, &one);
    }
    // Remove temp
    lp_integer_destruct(&one);
  }
  }

  if (ctx_trace_enabled(nra->ctx, "nra::terms")) {
    ctx_trace_printf(nra->ctx, "lp_polynomial_from_term: result = ");
    lp_polynomial_print(result, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, "\n");
  }

  return result;
}

lp_polynomial_t* lp_polynomial_from_term(term_t t, term_table_t* terms, int_hmap_t* term_to_lp_map, const lp_polynomial_context_t* lp_ctx, lp_integer_t* c) {
  term_kind_t kind;
  lp_polynomial_t* result = NULL;

  kind = term_kind(terms, t);
  switch (kind) {
  case ARITH_POLY:
    result = lp_polynomial_from_polynomial(poly_term_desc(terms, t), terms, term_to_lp_map, lp_ctx, c);
    break;
  case ARITH_CONSTANT: {
    // Get the constant numerator and denominator
    lp_integer_t lp_p;
    lp_integer_construct_from_int(lp_Z, &lp_p, 0);
    lp_integer_assign_yices_rational(&lp_p, c, rational_term_desc(terms, t));
    // polynomial a*x^0
    result = lp_polynomial_alloc();
    lp_polynomial_construct_simple(result, lp_ctx, &lp_p, 0, 0);
    // Remove temp
    lp_integer_destruct(&lp_p);
    break;
  }
  case POWER_PRODUCT:
    result = lp_polynomial_from_power_product(pprod_term_desc(terms, t), term_to_lp_map, lp_ctx, c);
    break;
  default: {
    // Constant 1
    lp_integer_t one;
    lp_integer_construct_from_int(lp_Z, &one, 1);
    // The variable
    int_hmap_pair_t* t_find = int_hmap_find(term_to_lp_map, t);
    assert(t_find != NULL);
    lp_variable_t lp_var = t_find->val;
    // Polynomial 1*x^1
    result = lp_polynomial_alloc();
    lp_polynomial_construct_simple(result, lp_ctx, &one, lp_var, 1);
    // Put 1 if requested
    if (c != NULL) {
      lp_integer_assign(lp_Z, c, &one);
    }
    // Remove temp
    lp_integer_destruct(&one);
  }
  }

  return result;
}

void lp_integer_construct_from_yices_rational(lp_integer_t* lp_p, lp_integer_t* lp_q, const rational_t* q) {
  if (lp_p != NULL) {
    rational_t q_num;
    q_init(&q_num);
    q_get_num(&q_num, q);
    mpq_t q_num_mpq;
    mpq_init(q_num_mpq);
    q_get_mpq(&q_num, q_num_mpq);
    lp_integer_construct_from_rational(lp_Z, lp_p, q_num_mpq);
    mpq_clear(q_num_mpq);
    q_clear(&q_num);
  }
  if (lp_q != NULL) {
    rational_t q_den;
    q_init(&q_den);
    q_get_den(&q_den, q);
    mpq_t q_den_mpq;
    mpq_init(q_den_mpq);
    q_get_mpq(&q_den, q_den_mpq);
    lp_integer_construct_from_rational(lp_Z, lp_q, q_den_mpq);
    mpq_clear(q_den_mpq);
    q_clear(&q_den);
  }
}

void lp_integer_assign_yices_rational(lp_integer_t* lp_p, lp_integer_t* lp_q, const rational_t* q) {
  lp_integer_destruct(lp_p);
  lp_integer_destruct(lp_q);
  lp_integer_construct_from_yices_rational(lp_p, lp_q, q);
}

void rational_construct_from_lp_integer(rational_t* q, const lp_integer_t* lp_z) {
  q_init(q);
  q_set_mpz(q, lp_z);
}

typedef struct {
  nra_plugin_t* nra;
  rba_buffer_t* b;
  term_table_t* terms;
} lp_polynomial_to_yices_term_nra_data;

void lp_polynomial_to_yices_traverse_f_nra(const lp_polynomial_context_t* ctx, lp_monomial_t* m, void* void_data) {

  lp_polynomial_to_yices_term_nra_data* data = (lp_polynomial_to_yices_term_nra_data*) void_data;

  if (ctx_trace_enabled(data->nra->ctx, "nra::terms")) {
    ctx_trace_printf(data->nra->ctx, "lp_polynomial_to_yices_term(");
    lp_monomial_print(ctx, m, ctx_trace_out(data->nra->ctx));
    ctx_trace_printf(data->nra->ctx, ")\n");
  }

  // Constant
  rational_t a;
  q_init(&a);
  q_set_mpz(&a, &m->a);

  if (m->n == 0) {
    // Just constant
    rba_buffer_add_const(data->b, &a);
  } else {
    // Actual monomial
    pp_buffer_t pp;
    init_pp_buffer(&pp, 0);
    uint32_t i = 0;
    for (i = 0; i < m->n; ++ i) {
      lp_variable_t lp_x = m->p[i].x;
      variable_t x = nra_plugin_get_variable_from_lp_variable(data->nra, lp_x);
      term_t x_term = variable_db_get_term(data->nra->ctx->var_db, x);
      pp_buffer_mul_varexp(&pp, x_term, m->p[i].d);
    }
    pprod_t* pprod = pprod_from_buffer(data->terms->pprods, &pp);
    term_t pp_term = pp_is_var(pprod) ? var_of_pp(pprod) : pprod_term(data->terms, pprod);
    rba_buffer_add_const_times_term(data->b, data->terms, &a, pp_term);
    delete_pp_buffer(&pp);
  }

  q_clear(&a);
}

term_t lp_polynomial_to_yices_term_nra( const lp_polynomial_t* lp_p, nra_plugin_t* nra) {

  term_table_t* terms = nra->ctx->terms;

  if (ctx_trace_enabled(nra->ctx, "nra::terms")) {
    ctx_trace_printf(nra->ctx, "lp_polynomial_to_yices_term(");
    lp_polynomial_print(lp_p, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, ")\n");
  }

  // Buffer for building
  lp_polynomial_to_yices_term_nra_data data;
  data.nra   = nra;
  data.b     = &nra->buffer;
  data.terms = terms;
  reset_rba_buffer(data.b);

  // Traverse and build
  lp_polynomial_traverse(lp_p, lp_polynomial_to_yices_traverse_f_nra, &data);

  // Make the term
  term_t result = mk_direct_arith_term(terms, data.b);

  if (ctx_trace_enabled(nra->ctx, "nra::terms")) {
    ctx_trace_printf(nra->ctx, "lp_polynomial_to_yices_term(");
    lp_polynomial_print(lp_p, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, ") => [%d] ", result);
    ctx_trace_term(nra->ctx, result);
  }

  return result;
}

typedef struct {
  int_hmap_t* lp_to_term_map;
  rba_buffer_t* b;
  term_table_t* terms;
} lp_polynomial_to_yices_term_data;

void lp_polynomial_to_yices_traverse_f(const lp_polynomial_context_t* ctx, lp_monomial_t* m, void* void_data) {

  lp_polynomial_to_yices_term_data* data = (lp_polynomial_to_yices_term_data*) void_data;

  // Constant
  rational_t a;
  q_init(&a);
  q_set_mpz(&a, &m->a);

  if (m->n == 0) {
    // Just constant
    rba_buffer_add_const(data->b, &a);
  } else {
    // Actual monomial
    pp_buffer_t pp;
    init_pp_buffer(&pp, 0);
    uint32_t i = 0;
    for (i = 0; i < m->n; ++ i) {
      lp_variable_t lp_x = m->p[i].x;
      int_hmap_pair_t* lp_x_find = int_hmap_find(data->lp_to_term_map, lp_x);
      assert(lp_x_find != NULL);
      term_t x_term = lp_x_find->val;
      pp_buffer_mul_varexp(&pp, x_term, m->p[i].d);
    }
    pprod_t* pprod = pprod_from_buffer(data->terms->pprods, &pp);
    term_t pp_term = pp_is_var(pprod) ? var_of_pp(pprod) : pprod_term(data->terms, pprod);
    rba_buffer_add_const_times_term(data->b, data->terms, &a, pp_term);
    delete_pp_buffer(&pp);
  }

  q_clear(&a);
}

term_t lp_polynomial_to_yices_term(const lp_polynomial_t* lp_p, term_table_t* terms, rba_buffer_t* b, int_hmap_t* lp_to_term_map) {

  // Buffer for building
  lp_polynomial_to_yices_term_data data;
  data.lp_to_term_map = lp_to_term_map;
  data.b = b;
  data.terms = terms;
  reset_rba_buffer(data.b);

  // Traverse and build
  lp_polynomial_traverse(lp_p, lp_polynomial_to_yices_traverse_f, &data);

  // Make the term
  term_t result = mk_direct_arith_term(terms, data.b);

  return result;
}


const mcsat_value_t* ensure_lp_value(const mcsat_value_t* value, mcsat_value_t* alternative) {
  lp_value_t lp_value;
  lp_rational_t rat_value;
  switch (value->type) {
  case VALUE_LIBPOLY:
    return value;
  case VALUE_RATIONAL:
    lp_rational_construct(&rat_value);
    q_get_mpq((rational_t*)&value->q, &rat_value);
    lp_value_construct(&lp_value, LP_VALUE_RATIONAL, &rat_value);
    mcsat_value_construct_lp_value(alternative, &lp_value);
    lp_value_destruct(&lp_value);
    lp_rational_destruct(&rat_value);
    return alternative;
  default:
    assert(false);
  }
  return NULL;
}

