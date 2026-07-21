/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
 * Get yices arith term from polynomial (direct version).
 */
term_t lp_polynomial_to_yices_arith_term(const lp_data_t *lp_data, const lp_polynomial_t* lp_p, term_table_t* terms, rba_buffer_t* b);

/**
 * Get yices finite field term from polynomial (direct version).
 */
term_t lp_polynomial_to_yices_arith_ff_term(const lp_data_t *lp_data, const lp_polynomial_t* lp_p, term_table_t* terms, rba_buffer_t* b);

/**
 * Ensure value is an lp_value. If not the passed alternative will be constructed to an equivalent lp_value.
 */
const mcsat_value_t* ensure_lp_value(const mcsat_value_t* value, mcsat_value_t* alternative);

#endif /* LP_UTILS_H_ */
