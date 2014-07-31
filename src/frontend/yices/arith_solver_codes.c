/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
