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

/*
 * CONVERT A MAPPING TO A MODEL
 */

/*
 * The mapping is given by two arrays of terms:
 * - var = array of uninterpreted terms
 * - map = array of constant terms
 * - map[i]'s type must be a subtype of var[i]'s type
 *
 * NOTE: function types are not supported.
 * - var[i] and map[i] must have primitive or tuple types
 */

#ifndef __MAP_TO_MODEL_H
#define __MAP_TO_MODEL_H

#include <stdint.h>
#include <stdbool.h>

#include "model/models.h"
#include "terms/terms.h"


/*
 * Build mdl from the mapping [var[i] := map[i]]
 * - mdl must be initialized
 *   every var[i] and map[i] must be a valid term defined in mdl->terms.
 *
 * - var[0 ... n-1] must all be uninterpreted terms
 *   map[0 ... n-1] must all be constant terms (of primitive or tuple type)
 *   map[i]'s type must be a subtype of var[i]'s type
 *
 * - if some 'x' occurs several times in array var then the first
 *   instance is used and the others are ignored.
 */
extern void build_model_from_map(model_t *model, uint32_t n, const term_t *var, const term_t *map);



#endif /* __MAP_TO_MODEL_H */
