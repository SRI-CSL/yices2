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
 * BIT-VECTOR POLYNOMIALS
 */

/*
 * Polynomials with bit-vector coefficients
 * represented as arrays of monomials.
 * Each monomial is a pair <coeff, variable>
 * - coeff is a bit-vector constant, stored as
 *   an array of 32bit words (cf. bv_constants).
 * - variable is a 32bit integer.
 *
 * More polynomial operations are defined in
 * bvarith_buffers.c.
 */

#ifndef __BV_POLYNOMIALS_H
#define __BV_POLYNOMIALS_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/polynomial_common.h"


/*
 * Polynomial structure:
 * - bitsize = number of bits
 * - width = coefficient size in words = ceil(bitsize/32)
 * - nterms = number of monomials
 * - mono = array of (nterms + 1) monomials
 * Polynomials are normalized:
 * - the coefficients are non zero.
 * - the monomials are sorted.
 * - mono[nterms].var contains the end marker max_idx
 */

// monomial
typedef struct {
  int32_t var;
  uint32_t *coeff;
} bvmono_t;

// polynomial
typedef struct {
  uint32_t nterms;
  uint32_t bitsize;
  uint32_t width;
  bvmono_t mono[0]; // actual size = nterms + 1
} bvpoly_t;


/*
 * Maximal number of terms in a polynomial
 */
#define MAX_BVPOLY_SIZE (((UINT32_MAX-sizeof(bvpoly_t))/sizeof(bvmono_t))-1)


/*
 * Seed used in the hash function (must be visible to bvarith_buffer).
 */
#define HASH_BVPOLY_SEED ((uint32_t) 0x13f23ef8)


/*
 * Allocate a bit-vector polynomial
 * - n = number of terms (excluding the end marker)
 * - n must be less than MAXBV_POLY_SIZE
 * - size = bitsize (must be positive and no more than YICES_MAX_BVSIZE)
 * The coefficients and variables are not initialized,
 * except the end marker.
 */
extern bvpoly_t *alloc_bvpoly(uint32_t n, uint32_t size);


/*
 * Free p and all the coefficients
 */
extern void free_bvpoly(bvpoly_t *p);


/*
 * Hash code
 */
extern uint32_t hash_bvpoly(bvpoly_t *p);


/*
 * Return the main variable of p (i.e., last variable)
 * - return null_idx if p is zero
 * - return const_idx is p is a constant
 */
extern int32_t bvpoly_main_var(bvpoly_t *p);


/*
 * Check whether p1 and p2 are equal
 */
extern bool equal_bvpoly(bvpoly_t *p1, bvpoly_t *p2);


/*
 * Check for simple disequality: return true if (p1 - p2) is a non-zero constant
 * bitvector.
 */
extern bool disequal_bvpoly(bvpoly_t *p1, bvpoly_t *p2);


/*
 * Check whethere (p1 - p2) is a constant
 */
extern bool delta_bvpoly_is_constant(bvpoly_t *p1, bvpoly_t *p2);


/*
 * Check whether p is of the form k + x for a non-zero constant k
 */
extern bool bvpoly_is_const_plus_var(bvpoly_t *p, int32_t x);


/*
 * Check whether p is a polynomial of ther form k + x for some non-zero constant k
 * and variable x.
 */
extern bool bvpoly_is_offset(bvpoly_t *p);


#endif /* __BV_POLYNOMIALS_H */
