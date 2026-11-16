/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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

