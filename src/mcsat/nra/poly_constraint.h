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

#include "mcsat/mcsat_types.h"
#include "mcsat/utils/lp_constraint_db.h"

typedef struct nra_plugin_s nra_plugin_t;

/** Try to resolve the two constraints with Fourier-Motzkin resolution */
bool poly_constraint_resolve_fm(const poly_constraint_t* c0, bool c0_negated, const poly_constraint_t* c1, bool c1_negated, nra_plugin_t* nra, ivector_t* out);

/** Compute an approximation of the constraint value with interval computation */
const mcsat_value_t* nra_poly_constraint_db_approximate(nra_plugin_t* nra, variable_t constraint_var);

/** Add a new constraint */
void nra_poly_constraint_create(nra_plugin_t *nra, variable_t constraint_var);
