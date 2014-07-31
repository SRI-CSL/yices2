/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TYPES AND CONSTANTS COMMON TO ALL POLYNOMIALS
 */

#ifndef __POLYNOMIAL_COMMON_H
#define __POLYNOMIAL_COMMON_H

/*
 * In compact representation, polynomials are represented
 * as arrays of monomials. Each monomial is a pair
 * (coefficient, variable indices), where coefficients are rationals
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

