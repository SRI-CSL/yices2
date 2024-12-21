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

#include "mcsat/utils/lp_utils.h"

#include "terms/rba_buffer_terms.h"
#include "terms/term_manager.h"

#include <poly/polynomial.h>
#include <poly/monomial.h>

#include "mcsat/value.h"

/**
 * Construct an p/q from a rational constant. If any of p or q are NULL, they are ignored.
 */
static
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

/**
 * Assign p/q from a yices rational constant.
 */
static
void lp_integer_assign_yices_rational(lp_integer_t* lp_p, lp_integer_t* lp_q, const rational_t* q) {
  if (lp_p != NULL) lp_integer_destruct(lp_p);
  if (lp_q != NULL) lp_integer_destruct(lp_q);
  lp_integer_construct_from_yices_rational(lp_p, lp_q, q);
}

/**
 * Create a libpoly polynomial from a yices power product. Returns lp_p = pp * c.
 *
 * @param term_to_lp_map a map from variables (terms) to variables (libpoly).
 */
static
lp_polynomial_t* lp_polynomial_from_power_product(lp_data_t *lp_data, pprod_t* pp, lp_integer_t* c) {
  const lp_int_ring_t* K = lp_data->lp_ctx->K;

  // The monomials
  lp_monomial_t lp_monomial;
  lp_monomial_construct(lp_data->lp_ctx, &lp_monomial);

  // Set monomial coefficient to 1
  lp_integer_t one;
  lp_integer_construct_from_int(K, &one, 1);
  lp_monomial_set_coefficient(lp_data->lp_ctx, &lp_monomial, &one);
  lp_integer_destruct(&one);

  // Get the product terms
  for (uint32_t i = 0; i < pp->len; ++ i) {
    lp_variable_t lp_var = lp_data_get_lp_variable_from_term(lp_data, pp->prod[i].var);
    lp_monomial_push(&lp_monomial, lp_var, pp->prod[i].exp);
  }

  lp_polynomial_t* result = lp_polynomial_new(lp_data->lp_ctx);
  lp_polynomial_add_monomial(result, &lp_monomial);

  if (c) {
    lp_integer_assign_int(K, c, 1);
  }

  lp_monomial_destruct(&lp_monomial);

  return result;
}

static
lp_polynomial_t* lp_polynomial_from_polynomial_integer(lp_data_t* lp_data, polynomial_t* p, term_table_t* terms, lp_integer_t* c) {
  const lp_int_ring_t* K = lp_data->lp_ctx->K;

  uint32_t i, j;
  lp_variable_t lp_var;

  lp_polynomial_t *result = lp_data_new_polynomial(lp_data);

  lp_integer_t a;
  lp_integer_construct(&a);

  lp_monomial_t lp_monomial;
  lp_monomial_construct(lp_data->lp_ctx, &lp_monomial);

  // Add up all the monomials
  for (i = 0; i < p->nterms; ++ i) {

    term_t product = p->mono[i].var;
    lp_monomial_clear(lp_data->lp_ctx, &lp_monomial);

    assert(q_is_integer(&p->mono[i].coeff));
    lp_integer_assign_yices_rational(&a, NULL, &p->mono[i].coeff);
    lp_monomial_set_coefficient(lp_data->lp_ctx, &lp_monomial, &a);

    if (product == const_idx) {
      // Constant polynomial, nothing to do
    } else if (term_kind(terms, product) == POWER_PRODUCT) {
      // Add all the variables
      pprod_t* pprod = pprod_for_term(terms, product);
      for (j = 0; j < pprod->len; ++j) {
        lp_var = lp_data_get_lp_variable_from_term(lp_data, pprod->prod[j].var);
        lp_monomial_push(&lp_monomial, lp_var, pprod->prod[j].exp);
      }
    } else {
      // Variable, or foreign term
      lp_var = lp_data_get_lp_variable_from_term(lp_data, product);
      lp_monomial_push(&lp_monomial, lp_var, 1);
    }

    // Add the monomial to the polynomial
    lp_polynomial_add_monomial(result, &lp_monomial);
  }

  // Remove temps
  lp_monomial_destruct(&lp_monomial);
  lp_integer_destruct(&a);

  if (c) {
    lp_integer_assign_int(K, c, 1);
  }

  return result;
}

/**
 * Create a libpoly polynomial from a yices polynomial. Returns the polynomial
 * lp_p and a positive integer constant c, such that lp_p = p * c. If c is NULL
 * it is ignored.
 */
static
lp_polynomial_t* lp_polynomial_from_polynomial_rational(lp_data_t* lp_data, polynomial_t* p, term_table_t* terms, lp_integer_t* c) {
  assert(lp_data->lp_ctx->K == lp_Z);

  uint32_t i, j;
  lp_variable_t lp_var;

  lp_polynomial_t *result = lp_data_new_polynomial(lp_data);

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
  lp_monomial_construct(lp_data->lp_ctx, &lp_monomial);

  // Add up all the monomials
  for (i = 0; i < p->nterms; ++ i) {

    term_t product = p->mono[i].var;
    lp_monomial_clear(lp_data->lp_ctx, &lp_monomial);

    // The constant (a/b)*lcm
    lp_integer_assign_yices_rational(&a, &b, &p->mono[i].coeff);
    lp_integer_div_exact(lp_Z, &b, &lcm, &b);
    lp_integer_mul(lp_Z, &a, &a, &b);
    lp_monomial_set_coefficient(lp_data->lp_ctx, &lp_monomial, &a);

    if (product == const_idx) {
      // Constant polynomial, nothing to do
    } else if (term_kind(terms, product) == POWER_PRODUCT) {
      // Add all the variables
      pprod_t* pprod = pprod_for_term(terms, product);
      for (j = 0; j < pprod->len; ++j) {
        lp_var = lp_data_get_lp_variable_from_term(lp_data, pprod->prod[j].var);
        lp_monomial_push(&lp_monomial, lp_var, pprod->prod[j].exp);
      }
    } else {
      // Variable, or foreign term
      lp_var = lp_data_get_lp_variable_from_term(lp_data, product);
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

static
lp_polynomial_t* lp_polynomial_from_constant_rational(lp_data_t* lp_data, rational_t* q, lp_integer_t* c) {
  // Get the constant numerator and denominator
  lp_integer_t lp_p;
  lp_integer_construct_from_int(lp_data->lp_ctx->K, &lp_p, 0);
  lp_integer_assign_yices_rational(&lp_p, c, q);
  // polynomial a*x^0
  lp_polynomial_t* result = lp_polynomial_alloc();
  lp_polynomial_construct_simple(result, lp_data->lp_ctx, &lp_p, 0, 0);
  // Remove temp
  lp_integer_destruct(&lp_p);

  return result;
}

static
lp_polynomial_t* lp_polynomial_from_constant_integer(lp_data_t* lp_data, rational_t *q, lp_integer_t* c) {
  const lp_int_ring_t *K = lp_data->lp_ctx->K;

  // Get the constant numerator and denominator
  lp_integer_t lp_p;
  lp_integer_construct_from_int(K, &lp_p, 0);
  assert(q_is_integer(q));
  lp_integer_assign_yices_rational(&lp_p, NULL, q);
  // polynomial a*x^0
  lp_polynomial_t* result = lp_polynomial_alloc();
  lp_polynomial_construct_simple(result, lp_data->lp_ctx, &lp_p, 0, 0);
  // Remove temp
  lp_integer_destruct(&lp_p);

  if (c) {
    lp_integer_assign_int(K, c, 1);
  }

  return result;
}

static
lp_polynomial_t* lp_polynomial_from_variable(lp_data_t *lp_data, lp_variable_t lp_var, lp_integer_t *c) {
  const lp_int_ring_t *K = lp_data->lp_ctx->K;

  // Constant 1
  lp_integer_t one;
  lp_integer_construct_from_int(K, &one, 1);
  // Polynomial 1*x^1
  lp_polynomial_t* result = lp_polynomial_alloc();
  lp_polynomial_construct_simple(result, lp_data->lp_ctx, &one, lp_var, 1);
  // Put 1 if requested
  if (c != NULL) {
    lp_integer_assign(lp_Z, c, &one);
  }
  // Remove temp
  lp_integer_destruct(&one);

  return result;
}

lp_polynomial_t* lp_polynomial_from_term(lp_data_t* lp_data, term_t t, term_table_t* terms, lp_integer_t* c) {
  const lp_int_ring_t *K = lp_data->lp_ctx->K;
  (void)K;

  switch (term_kind(terms, t)) {
  case ARITH_POLY:
    assert(K == lp_Z);
    return lp_polynomial_from_polynomial_rational(lp_data, poly_term_desc(terms, t), terms, c);
  case ARITH_FF_POLY:
    assert(K != lp_Z);
    return lp_polynomial_from_polynomial_integer(lp_data, finitefield_poly_term_desc(terms, t), terms, c);
  case ARITH_CONSTANT:
    assert(K == lp_Z);
    return lp_polynomial_from_constant_rational(lp_data, rational_term_desc(terms, t), c);
  case ARITH_FF_CONSTANT:
    assert(K != lp_Z);
    return lp_polynomial_from_constant_integer(lp_data, finitefield_term_desc(terms, t), c);
  case POWER_PRODUCT:
    return lp_polynomial_from_power_product(lp_data, pprod_term_desc(terms, t), c);
  default:
    return lp_polynomial_from_variable(lp_data, lp_data_get_lp_variable_from_term(lp_data, t), c);
  }
}

typedef struct {
  const lp_data_t* lp_data;
  rba_buffer_t* b;
  term_table_t* terms;
} lp_polynomial_to_yices_term_data;

static
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
    for (uint32_t i = 0; i < m->n; ++ i) {
      lp_variable_t lp_x = m->p[i].x;
      term_t x_term = lp_data_get_term_from_lp_variable(data->lp_data, lp_x);
      pp_buffer_mul_varexp(&pp, x_term, m->p[i].d);
    }
    pprod_t* pprod = pprod_from_buffer(data->terms->pprods, &pp);
    term_t pp_term = pp_is_var(pprod) ? var_of_pp(pprod) : pprod_term(data->terms, pprod);
    rba_buffer_add_const_times_term(data->b, data->terms, &a, pp_term);
    delete_pp_buffer(&pp);
  }

  q_clear(&a);
}

static
void lp_polynomial_to_yices_term(const lp_data_t *lp_data, const lp_polynomial_t* lp_p, term_table_t* terms, rba_buffer_t* b) {

  // Buffer for building
  lp_polynomial_to_yices_term_data data;
  data.lp_data = lp_data;
  data.b = b;
  data.terms = terms;

  reset_rba_buffer(data.b);

  // Traverse and build
  lp_polynomial_traverse(lp_p, lp_polynomial_to_yices_traverse_f, &data);
}

term_t lp_polynomial_to_yices_arith_term(const lp_data_t *lp_data, const lp_polynomial_t* lp_p, term_table_t* terms, rba_buffer_t* b) {
  lp_polynomial_to_yices_term(lp_data, lp_p, terms, b);

  // Make the term
  return mk_direct_arith_term(terms, b);
}

term_t lp_polynomial_to_yices_arith_ff_term(const lp_data_t *lp_data, const lp_polynomial_t* lp_p, term_table_t* terms, rba_buffer_t* b) {
  lp_polynomial_to_yices_term(lp_data, lp_p, terms, b);

  // assure it's a finite field lp_data
  assert(lp_data_get_ring(lp_data));

  rational_t mod;
  q_init(&mod);
  q_set_mpz(&mod, &lp_data_get_ring(lp_data)->M);

  // Make the term
  term_t result = mk_direct_arith_ff_term(terms, b, &mod);
  q_clear(&mod);

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
