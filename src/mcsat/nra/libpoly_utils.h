/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#pragma once

#include <poly/polynomial.h>

#include "mcsat/nra/nra_plugin_internal.h"
#include "terms/polynomials.h"

/**
 * Create a lipoly polynomial from a yices polynomial. Returns the polynomial
 * lp_p and a positive integer constant c, such that lp_p = p * c. If c is NULL
 * it is ignored.
 */
lp_polynomial_t* lp_polynomial_from_polynomial(nra_plugin_t* nra, polynomial_t* p, lp_integer_t* c);

/**
 * Create a libpoly polynomial from a yices power product. Returns lp_p = pp * c.
 */
lp_polynomial_t* lp_polynomial_from_power_product(nra_plugin_t* nra, pprod_t * pp, lp_integer_t* c);

/**
 * Create a libpoly polynomial from a yices term. Returns the polynomial
 * lp_p and a positive integer constant c, such that lp_p = p * c. If c is
 * NULL it is ignored.
 */
lp_polynomial_t* lp_polynomial_from_term(nra_plugin_t* nra, term_table_t* terms, term_t p, lp_integer_t* c);

/**
 * Construct an p/q from a rational constant. If any of p or q are
 */
void lp_integer_construct_from_yices_rational(lp_integer_t* lp_p, lp_integer_t* lp_q, const rational_t* q);

/**
 * Assign p/q from a yices rational constant.
 */
void lp_integer_assign_yices_rational(lp_integer_t* lp_p, lp_integer_t* lp_q, const rational_t* q);

/**
 * Construct a yices rational from lp_integer.
 */
void rational_construct_from_lp_integer(rational_t* q, const lp_integer_t* lp_z);

/**
 * Get yices term from polynomial.
 */
term_t lp_polynomial_to_yices_term(nra_plugin_t* nra, const lp_polynomial_t* lp_p);
