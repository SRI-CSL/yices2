/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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
 * BUFFERS FOR FACTORING BIT-VECTOR EXPRESSIONS
 */

/*
 * We can attempt to factor and simplify expressions that mix
 * bitvector products and left-shift. This corresponds to
 * expressions built form the following operators:
 *   (bvmul x y)
 *   (bvshl x y)
 *   (bvneg x)
 * where x, y have type (bitvector n).
 *
 * For can see these expressions as product of integers modulo 2^n:
 *   (bvmul x y) = x * y
 *   (bvshl x y) = x * 2^y
 *   (bvneg x)   = -1 * x
 *
 * In general, we can rewrite these expressions in the following form:
 *   a * product * 2 ^ exponent
 * where a is an n-bit constant
 *       product is a power product: x_1^d_1  ... x_k^d_k
 *       exponent is a polynomial: a_1 y_1 + ... + a_j y_j
 *
 * A bvfactor_buffer is a data structure to store these three components.
 */

#ifndef __BVFACTOR_BUFFERS_H
#define __BVFACTOR_BUFFERS_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/bv_constants.h"
#include "terms/bvpoly_buffers.h"
#include "terms/power_products.h"

/*
 * Buffer components:
 * - bitsize = number of bits in all factors
 * - width - ceil(bitsize/32)
 * - total_degree = degree of the power products
 * - constant64 = constant part (if bitsize <= 64)
 * - constant = constant part (if bitsize > 64)
 * - product = power product
 * - exponent = polynomial exponent
 *
 * - aux = a temporary buffer for computations
 */
typedef struct bvfactor_buffer_s {
  uint32_t bitsize;
  uint32_t width;
  uint64_t total_degree;
  uint64_t constant64;
  bvconstant_t constant;
  pp_buffer_t product;
  bvpoly_buffer_t exponent;

  bvconstant_t aux;
} bvfactor_buffer_t;


/*
 * Initialize: this allocates the components and set bitsize to 0
 */
extern void init_bvfactor_buffer(bvfactor_buffer_t *b);

/*
 * Reset and prepare to store products
 * - n = number of bits
 * - this sets the constant to 1,
 *   product empty, and exponent 0
 */
extern void reset_bvfactor_buffer(bvfactor_buffer_t *b, uint32_t n);

/*
 * Delete: free memory
 */
extern void delete_bvfactor_buffer(bvfactor_buffer_t *b);


/*
 * Initialize b and copy b1 into b
 */
extern void bvfactor_buffer_init_copy(bvfactor_buffer_t *b, bvfactor_buffer_t *b1);


/*
 * Multiply by x^d (for some variable x)
 */
extern void bvfactor_buffer_mul(bvfactor_buffer_t *b, int32_t x, uint32_t d);


/*
 * Multiply by (2^y)^d
 */
extern void bvfactor_buffer_exp(bvfactor_buffer_t *b, int32_t y, uint32_t d);

/*
 * Multiply by (2^(a * y))^d where a is an n-bit constant
 * - two variants: mulexp64 if n <= 64 or mulexp if n > 64
 * - for mulexp, a must be given as an array of w words where w = ceil(n/32)
 */
extern void bvfactor_buffer_mulexp(bvfactor_buffer_t *b, uint32_t *a, int32_t y, uint32_t d);
extern void bvfactor_buffer_mulexp64(bvfactor_buffer_t *b, uint64_t a, int32_t y, uint32_t d);


/*
 * Multiply by a^d where a is an n-bit constant
 */
extern void bvfactor_buffer_mulconst(bvfactor_buffer_t *b, uint32_t *a, uint32_t d);
extern void bvfactor_buffer_mulconst64(bvfactor_buffer_t *b, uint64_t a, uint32_t d);


/*
 * Normalize:
 * - reduce the constant modulo 2^n
 * - normalize the product and exponent (cf. power_products.h and bvpoly_buffers.h)
 */
extern void bvfactor_buffer_normalize(bvfactor_buffer_t *b);


/*
 * Check whether two buffers are equal
 * - both buffers must be normalized and have the same bitsize
 */
extern bool bvfactor_buffer_equal(bvfactor_buffer_t *b1, bvfactor_buffer_t *b2);


/*
 * Check whether two buffers have equal exponents
 * - both buffers must be normalized and have the same bitsize
 */
extern bool bvfactor_buffer_equal_exponents(bvfactor_buffer_t *b1, bvfactor_buffer_t *b2);


/*
 * Compute the common factors of b1->product and b2->product.
 * - both b1 and b2 must be normalized
 * - store the result in pbuffer
 * - pbuffer must be initialized
 * - the result is normalized
 */
extern void bvfactor_buffer_common_factors(pp_buffer_t *pbuffer, bvfactor_buffer_t *b1, bvfactor_buffer_t *b2);

/*
 * Variant: compute the common factors of b1[0 ..n1-1] and b2[0 ... n2-1]
 * - all factor buffers must be normalized
 * - the result is stored in pbuffer
 */
extern void bvfactor_buffer_array_common_factors(pp_buffer_t *pbuffer, bvfactor_buffer_t *b1, uint32_t n1,
						 bvfactor_buffer_t *b2, uint32_t n2);


/*
 * Reduce: divide b->product by pbuffer
 * - pbuffer must be normalized and must be a divisor of b->product
 */
extern void bvfactor_buffer_reduce(bvfactor_buffer_t *b, pp_buffer_t *pbuffer);

/*
 * Divide b->product by x
 */
extern void bvfactor_buffer_reduce_by_var(bvfactor_buffer_t *b, int32_t x);

/*
 * Check whether b->product is linear (i.e., degree <= 1)
 * - b must be normalized
 */
extern bool bvfactor_buffer_is_linear(bvfactor_buffer_t *b);

/*
 * Check whether b->product is constant (i.e., degree = 0)
 * - b must be normalized
 */
static inline bool bvfactor_buffer_product_is_one(bvfactor_buffer_t *b) {
  return b->product.len == 0;
}

/*
 * Check whether b->product is reduced to a single variable (i.e., degree = 1)
 * - b must be normalized
 */
extern bool bvfactor_buffer_is_var(bvfactor_buffer_t *b);

/*
 * Get the variable of b->product if b->product has degree 1
 */
extern int32_t bvfactor_buffer_get_var(bvfactor_buffer_t *b);

/*
 * Check whether the constant is zero
 * - b must be normalized
 */
extern bool bvfactor_buffer_is_zero(bvfactor_buffer_t *b);

/*
 * Check whether the exponent is zero
 * - b must be normalized
 */
static inline bool bvfactor_buffer_exponent_is_zero(bvfactor_buffer_t *b) {
  return bvpoly_buffer_is_zero(&b->exponent);
}


#endif /* __BVFACTOR_BUFFERS_H */

