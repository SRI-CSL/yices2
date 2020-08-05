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
 * QUANT SOLVER PARAMETERS
 */


#ifndef __QUANT_PARAMETERS_H
#define __QUANT_PARAMETERS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>
#include <string.h>

/*
 * Tags identifying the iteration order
 */
typedef enum {
  ITERATE_UNKNOWN = -1,
  ITERATE_ALL = 0,
  ITERATE_EPSILONGREEDY = 1,
  ITERATE_RANDOM = 2,
  ITERATE_GREEDY = 3,
} iterate_kind_t;


/*
 * Default bounds
 */
#define DEFAULT_MAX_INSTANCES_PER_ROUND   10
#define DEFAULT_MAX_INSTANCES_PER_SEARCH  100
#define DEFAULT_MAX_INSTANCES             100000

#define DEFAULT_MAX_ROUNDS_PER_SEARCH     50
#define DEFAULT_MAX_SEARCH                5000

#define DEFAULT_EMATCH_MODE              ITERATE_EPSILONGREEDY




/*
 * Test whether ematch mode is known and supported.
 * - mode = ematch iteration mode to use
 * - return mode (as positive integer) if this mode is supported.
 * - return -1 otherwise.
 */
extern int32_t supported_ematch_mode(const char *mode);




#endif /* __QUANT_PARAMETERS_H */
