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
 * Conversion from solver names to an integer code
 */

#include <stdint.h>
#include <string.h>
#include <assert.h>

#include "frontend/yices/arith_solver_codes.h"


/*
 * Table of names in lexicographic order
 */
#define NUM_ARITH_SOLVER_NAMES NUM_ARITH_CODES

static const char * const arith_solver_names[NUM_ARITH_SOLVER_NAMES] = {
  "auto",
  "floyd-warshall",
  "simplex",
};


/*
 * Converse table: arith_code[i] = code for arith_solver_name[i]
 * - this may be useful later if different names map to the same solver
 */
static const arith_code_t arith_code[NUM_ARITH_SOLVER_NAMES] = {
  ARITH_AUTO,
  ARITH_FLOYD_WARSHALL,
  ARITH_SIMPLEX,
};



/*
 * Return the code for the given name.
 * - return ARITH_UNKNOWN if the name is not recognized
 */
arith_code_t arith_solver_code(const char *arith_name) {
  uint32_t i;
  arith_code_t code;

  code = ARITH_UNKNOWN;
  for (i=0; i<NUM_ARITH_SOLVER_NAMES; i++) {
    if (strcmp(arith_name, arith_solver_names[i]) == 0) {
      code = arith_code[i];
      break;
    }
  }

  return code;
}
