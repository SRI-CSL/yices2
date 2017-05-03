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
 * TYPES AND CONSTANTS COMMON TO ALL POLYNOMIALS
 */

#ifndef __POLYNOMIAL_COMMON_H
#define __POLYNOMIAL_COMMON_H

/*
 * In compact representation, polynomials are represented
 * as arrays of monomials. Each monomial is a pair
 * (coefficient, variable index), where coefficients are rationals
 * or bitvector constants.
 *
 * Special variable indices are used:
 * - null_idx = -1
 * - const_idx = 0: constant
 * - max_idx = INT32_MAX: end marker
 */
enum {
  null_idx = -1,
  const_idx = 0,
  max_idx = INT32_MAX,
};


/*
 * Type of user-provided comparison functions.  This can be used to
 * normalize polynomials using a different ordering than the default.
 *
 * A comparison function cmp is called with three parameters:
 * - aux is a generic pointer provided to the sort function
 * - x and y are two distinct variable indices
 * - cmp(aux, x, y) must return true if x < y.
 *
 * The ordering must satisfy the following constraints:
 * - const_idx is smaller than any other variable
 * - max_idx is larger than any other variable
 */
typedef bool (*var_cmp_fun_t)(void *data, int32_t x, int32_t y);


#endif /* __POLYNOMIAL_COMMON_H */

