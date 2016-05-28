/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/nra/libpoly_utils.h"
#include "mcsat/nra/nra_plugin_internal.h"
#include "mcsat/tracing.h"

#include "terms/balanced_arith_buffers.h"
#include "terms/rba_buffer_terms.h"
#include "terms/term_manager.h"

#include <poly/monomial.h>

#include <gmp.h>

lp_polynomial_t* lp_polynomial_from_power_product(nra_plugin_t* nra, pprod_t* pp, lp_integer_t* c) {

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

lp_polynomial_t* lp_polynomial_from_polynomial(nra_plugin_t* nra, polynomial_t* p, lp_integer_t* c) {

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

lp_polynomial_t* lp_polynomial_from_term(nra_plugin_t* nra, term_table_t* terms, term_t t, lp_integer_t* c) {
  term_kind_t kind;
  lp_polynomial_t* result;

  result = 0;

  if (ctx_trace_enabled(nra->ctx, "nra::terms")) {
    ctx_trace_printf(nra->ctx, "lp_polynomial_from_term: t = ");
    ctx_trace_term(nra->ctx, t);
  }

  kind = term_kind(terms, t);
  switch (kind) {
  case ARITH_POLY:
    result = lp_polynomial_from_polynomial(nra, poly_term_desc(terms, t), c);
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
    result = lp_polynomial_from_power_product(nra, pprod_term_desc(terms, t), c);
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
} lp_polynomial_to_yices_term_data;

void lp_polynomial_to_yices_traverse_f(const lp_polynomial_context_t* ctx, lp_monomial_t* m, void* void_data) {

  lp_polynomial_to_yices_term_data* data = (lp_polynomial_to_yices_term_data*) void_data;

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

term_t lp_polynomial_to_yices_term(nra_plugin_t* nra, const lp_polynomial_t* lp_p) {

  term_table_t* terms = nra->ctx->terms;

  if (ctx_trace_enabled(nra->ctx, "nra::terms")) {
    ctx_trace_printf(nra->ctx, "lp_polynomial_to_yices_term(");
    lp_polynomial_print(lp_p, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, ")\n");
  }

  // Buffer for building
  lp_polynomial_to_yices_term_data data;
  data.nra   = nra;
  data.b     = &nra->buffer;
  data.terms = terms;
  reset_rba_buffer(data.b);

  // Traverse and build
  lp_polynomial_traverse(lp_p, lp_polynomial_to_yices_traverse_f, &data);

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

