/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Codes to identify which arithmetic solver to use
 */

#ifndef __ARITH_SOLVER_CODES_H
#define __ARITH_SOLVER_CODES_H


/*
 * Current codes
 */
typedef enum {
  ARITH_SIMPLEX,
  ARITH_FLOYD_WARSHALL,
  ARITH_AUTO,
  ARITH_UNKNOWN, // error codes
} arith_code_t;


// number of known codes
#define NUM_ARITH_CODES ARITH_UNKNOWN


/*
 * Convert a name to an arith_code:
 * - the valid names are "simplex", "floyd-warshall", or "auto"
 * - all lower case
 */
extern arith_code_t arith_solver_code(const char *arith_name);


#endif /* __ARITH_SOLVER_CODES_H */
