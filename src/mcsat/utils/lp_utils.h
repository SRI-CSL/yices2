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

#ifndef LP_UTILS_H_
#define LP_UTILS_H_

#include <poly/poly.h>

#include "mcsat/utils/lp_data.h"

/**
 * Create a libpoly polynomial from a yices term. Returns the polynomial
 * lp_p and a positive integer constant c, such that lp_p = p * c. If c is
 * NULL it is ignored.
 */
lp_polynomial_t* lp_polynomial_from_term(lp_data_t* lp_data, term_t t, term_table_t* terms, lp_integer_t* c);

/**
 * Get yices term from polynomial (direct version).
 */
term_t lp_polynomial_to_yices_term(const lp_data_t *lp_data, const lp_polynomial_t* lp_p, term_table_t* terms, rba_buffer_t* b);

/**
 * Construct a yices rational from lp_integer.
 */
void rational_construct_from_lp_integer(rational_t* q, const lp_integer_t* lp_z);

/**
 * Ensure value is an lp_value. If not the passed alternative will be constructed to an equivalent lp_value.
 */
const mcsat_value_t* ensure_lp_value(const mcsat_value_t* value, mcsat_value_t* alternative);

#endif /* LP_UTILS_H_ */
