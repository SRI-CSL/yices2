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

#include "model/models.h"
#include "utils/int_vectors.h"
#include "utils/int_hash_sets.h"

/*
 * Project a set of literals.
 *
 * Given a set of literals L satisfied by the model M, this function returns a new set of literals L' such that
 *
 * - L' is aslo satisfied by M
 * - L' only contains the variables in vars_to_keep;
 * - any satisfying assignment of L' can be extended to an assignment of L
 *
 * @param literal the literals L above
 * @param mdl the model M above
 * @param vars all variables of L
 * @param vars_to_keep the variables allowed in L' (subset of vars)
 *
 * On return the literals vector will contain L'.
 *
 * @return 0 on success, negative if failure (e.g., integer arithmetic).
 */
int32_t nra_project_arith_literals(ivector_t* literals, model_t* mdl, ivector_t* vars, int_hset_t* vars_to_keep);
