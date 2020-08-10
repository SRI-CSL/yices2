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



#include "solvers/quant/quant_parameters.h"



/*
 * Test whether ematch mode is known and supported.
 * - mode = ematch iteration mode to use
 * - return mode (as positive integer) if this mode is supported.
 * - return -1 otherwise.
 */
int32_t supported_ematch_mode(const char *mode) {
  if (strcmp("all", mode) == 0) {
    return ITERATE_ALL;
  }
  if (strcmp("epsilongreedy", mode) == 0) {
    return ITERATE_EPSILONGREEDY;
  }
  if (strcmp("random", mode) == 0) {
    return ITERATE_RANDOM;
  }

  return ITERATE_UNKNOWN;
}

