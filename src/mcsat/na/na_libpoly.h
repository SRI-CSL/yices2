/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef NA_LIBPOLY_H_
#define NA_LIBPOLY_H_

#include "mcsat/mcsat_types.h"
#include "mcsat/utils/lp_constraint_db.h"

#include <poly/poly.h>

typedef struct na_plugin_s na_plugin_t;

/**
 * Create a libpoly polynomial from a yices term. Returns the polynomial
 * lp_p and a positive integer constant c, such that lp_p = p * c. If c is
 * NULL it is ignored.
 */
lp_polynomial_t* lp_polynomial_from_term_na(na_plugin_t* na, term_t p, lp_integer_t* c);

/**
 * Get yices term from polynomial (NA plugin wrapper).
 */
term_t lp_polynomial_to_yices_term_na(na_plugin_t *na, const lp_polynomial_t *lp_p);

/** Compute an approximation of the constraint value with interval computation */
const mcsat_value_t* na_poly_constraint_db_approximate(na_plugin_t* na, variable_t constraint_var);

/** Add a new constraint */
void na_poly_constraint_add(na_plugin_t *na, variable_t constraint_var);

/** Create a new constraint */
poly_constraint_t* na_poly_constraint_create(na_plugin_t *na, variable_t constraint_var);

#endif /* NA_LIBPOLY_H_ */
