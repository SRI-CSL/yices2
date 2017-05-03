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
