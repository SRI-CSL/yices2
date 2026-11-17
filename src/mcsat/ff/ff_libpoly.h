/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef FF_LIBPOLY_H_
#define FF_LIBPOLY_H_

#include "mcsat/mcsat_types.h"
#include "mcsat/utils/lp_constraint_db.h"

#include <poly/poly.h>

typedef struct ff_plugin_s ff_plugin_t;

/**
 * Create a libpoly polynomial from a yices term. Returns the polynomial
 * lp_p and a positive integer constant c, such that lp_p = p * c. If c is
 * NULL it is ignored.
 */
lp_polynomial_t* lp_polynomial_from_term_ff(ff_plugin_t* ff, term_t t, lp_integer_t* c);

/**
 * Get yices term from polynomial (FF plugin wrapper).
 */
term_t lp_polynomial_to_yices_term_ff(ff_plugin_t *ff, const lp_polynomial_t *lp_p);

/** Add a new constraint */
void ff_poly_constraint_add(ff_plugin_t *ff, variable_t constraint_var);

/** Create a new constraint */
poly_constraint_t* ff_poly_constraint_create(ff_plugin_t *ff, variable_t constraint_var);

#endif /* FF_LIBPOLY_H_ */
