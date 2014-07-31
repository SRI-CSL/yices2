/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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

#include "terms/terms.h"
#include "model/models.h"


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
