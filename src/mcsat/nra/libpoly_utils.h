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
 
#pragma once

#include <poly/polynomial.h>

#include "mcsat/nra/nra_plugin_internal.h"
#include "terms/polynomials.h"

/**
 * Create a lipoly polynomial from a yices polynomial. Returns the polynomial
 * lp_p and a positive integer constant c, such that lp_p = p * c. If c is NULL
 * it is ignored.
 */
lp_polynomial_t* lp_polynomial_from_polynomial_nra(nra_plugin_t* nra, polynomial_t* p, lp_integer_t* c);

/**
 * Create a libpoly polynomial from a yices power product. Returns lp_p = pp * c.
 */
lp_polynomial_t* lp_polynomial_from_power_product_nra(nra_plugin_t* nra, pprod_t * pp, lp_integer_t* c);

/**
 * Create a libpoly polynomial from a yices term. Returns the polynomial
 * lp_p and a positive integer constant c, such that lp_p = p * c. If c is
 * NULL it is ignored.
 */
lp_polynomial_t* lp_polynomial_from_term_nra(nra_plugin_t* nra, term_t p, lp_integer_t* c);

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
 * Get yices term from polynomial (NRA plugin version).
 */
term_t lp_polynomial_to_yices_term_nra(const lp_polynomial_t* lp_p, nra_plugin_t* nra);

/**
 * Get yices term from polynomial (direct version).
 */
term_t lp_polynomial_to_yices_term(const lp_polynomial_t* lp_p, term_table_t* terms, rba_buffer_t* b, int_hmap_t* lp_to_term_map);

/**
 * Ensure value is an lp_value. If not the passed alternative will be constructed to an equivalent lp_value.
 */
const mcsat_value_t* ensure_lp_value(const mcsat_value_t* value, mcsat_value_t* alternative);
