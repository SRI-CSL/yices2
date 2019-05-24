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

#include <assert.h>

#include "yices_limits.h"

#include "terms/bvfactor_buffers.h"
#include "terms/bv64_constants.h"
#include "utils/int_powers.h"


/*
 * Initialize: this allocates the components and set bitsize to 0
 */
void init_bvfactor_buffer(bvfactor_buffer_t *b) {
  b->bitsize = 0;
  b->width = 0;
  b->total_degree = 0;
  b->constant64 = 0;
  init_bvconstant(&b->constant);
  init_pp_buffer(&b->product, 10);
  init_bvpoly_buffer(&b->exponent);
  init_bvconstant(&b->aux);
}


/*
 * Reset and prepare to store products
 * - n = number of bits
 * - this sets the constant to 1,
 *   product empty a and exponent 0
 */
void reset_bvfactor_buffer(bvfactor_buffer_t *b, uint32_t n) {
  assert(0 < n && n <= YICES_MAX_BVSIZE);
  b->bitsize = n;
  b->width = (n + 31) >> 5;
  b->total_degree = 0;
  if (n <= 64) {
    b->constant64 = 1;
  } else {
    bvconstant_copy64(&b->constant, n, 1);
  }
  pp_buffer_reset(&b->product);
  reset_bvpoly_buffer(&b->exponent, n);
}


/*
 * Delete: free memory
 */
void delete_bvfactor_buffer(bvfactor_buffer_t *b) {
  delete_bvconstant(&b->constant);
  delete_pp_buffer(&b->product);
  delete_bvpoly_buffer(&b->exponent);
  delete_bvconstant(&b->aux);
}



/*
 * Multiply by x^d (for some variable x)
 */
void bvfactor_buffer_mul(bvfactor_buffer_t *b, int32_t x, uint32_t d) {
  b->total_degree += d;
  pp_buffer_push_varexp(&b->product, x, d);
}


/*
 * Multiply by (2^y)^d: add d*y to the exponent
 */
void bvfactor_buffer_exp(bvfactor_buffer_t *b, int32_t y, uint32_t d) {
  if (b->bitsize <= 64) {
    bvpoly_buffer_add_mono64(&b->exponent, y, (uint64_t) d);
  } else {
    bvconstant_copy64(&b->aux, b->bitsize, (uint64_t) d);
    bvpoly_buffer_add_monomial(&b->exponent, y, b->aux.data);
  }
}


/*
 * Multiply by 2^(a * y)^d where a is an n-bit constant
 * - two variants: mulexp64 if n <= 64 or mulexp if n > 64
 * - for mulexp, a must be given as an array of w words where w = ceil(n/32)
 *
 * We add (a * d) * y to the exponent
 */
void bvfactor_buffer_mulexp(bvfactor_buffer_t *b, uint32_t *a, int32_t y, uint32_t d) {
  bvconstant_copy64(&b->aux, b->bitsize, (uint64_t) d);
  bvpoly_buffer_addmul_monomial(&b->exponent, y, a, b->aux.data);
}

void bvfactor_buffer_mulexp64(bvfactor_buffer_t *b, uint64_t a, int32_t y, uint32_t d) {
  bvpoly_buffer_addmul_mono64(&b->exponent, y, a, (uint64_t) d);
}


/*
 * Multiply by a^d where a is an n-bit constant
 */
void bvfactor_buffer_mulconst(bvfactor_buffer_t *b, uint32_t *a, uint32_t d) {
  bvconst_mulpower(b->constant.data, b->width, a, d);
}

void bvfactor_buffer_mulconst64(bvfactor_buffer_t *b, uint64_t a, uint32_t d) {
  b->constant64 *= upower64(a, d);
}


/*
 * Normalize:
 * - reduce the constant modulo 2^n
 * - nornalize the product and exponent (cf. power_products.h and bvpoly_buffers.h)
 */
void bvfactor_buffer_normalize(bvfactor_buffer_t *b) {
  uint32_t n;

  n = b->bitsize;
  if (n <= 64) {
    b->constant64 = norm64(b->constant64, n);
  } else {
    bvconst_normalize(b->constant.data, n);
  }
  pp_buffer_normalize(&b->product);
  normalize_bvpoly_buffer(&b->exponent);
}


/*
 * Check whether two buffers are equal
 * - both buffers must be nornalized and have the same bitsizea
 */
bool bvfactor_buffer_equal(bvfactor_buffer_t *b1, bvfactor_buffer_t *b2) {
  uint32_t n, w;

  assert(b1->bitsize == b2->bitsize);

  n = b1->bitsize;
  if (n <= 64) {
    if (b1->constant64 != b2->constant64) return false;
  } else {
    w = b1->width;
    assert(w == b2->width);
    if (bvconst_neq(b1->constant.data, b2->constant.data, w)) return false;
  }

  return pp_buffer_equal(&b1->product, &b2->product) &&
    bvpoly_buffer_equal(&b1->exponent, &b2->exponent);
}


