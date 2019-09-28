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
 *   product empty, and exponent 0
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
 * Initialize b and copy b1 into b
 */
void bvfactor_buffer_init_copy(bvfactor_buffer_t *b, bvfactor_buffer_t *b1) {
  uint32_t n;

  init_bvfactor_buffer(b);

  n = b1->bitsize;
  b->bitsize = n;
  b->width = (n + 31) >> 5;
  b->total_degree = b1->total_degree;
  if (n <= 64) {
    b->constant64 = b1->constant64;
  } else {
    bvconstant_copy(&b->constant, n, b1->constant.data);
  }
  pp_buffer_copy(&b->product, &b1->product);
  reset_bvpoly_buffer(&b->exponent, n);
  bvpoly_buffer_add_buffer(&b->exponent, &b1->exponent);
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
  bvpoly_buffer_t *e;
  uint64_t d;
  uint32_t *g;
  uint32_t n;

  n = b->bitsize;

  // normalize the product
  pp_buffer_normalize(&b->product);

  // normalize the exponent
  e = &b->exponent;
  normalize_bvpoly_buffer(e);

  /*
   * if the exponent is a non-zero constant d,
   * multiply b->constant64 or b->consant by 2^d
   */
  if (bvpoly_buffer_is_constant(e) && !bvpoly_buffer_is_zero(e)) {
    if (n <= 64) {
      d = bvpoly_buffer_coeff64(e, 0);
      b->constant64 = bvconst64_lshl(b->constant64, d, n);
      assert(b->constant64 == norm64(b->constant64, n));
    } else {
      g = bvpoly_buffer_coeff(e, 0);
      bvconst_lshl_inplace(b->constant.data, g, n);
      assert(bvconstant_is_normalized(&b->constant));
    }
    reset_bvpoly_buffer(e, n);
  } else {
    if (n <= 64) {
      b->constant64 = norm64(b->constant64, n);
    } else {
      bvconst_normalize(b->constant.data, n);
    }
  }
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



/*
 * Check whether two buffers have equal exponents
 * - both buffers must be normalized and have the same bitsize
 */
bool bvfactor_buffer_equal_exponents(bvfactor_buffer_t *b1, bvfactor_buffer_t *b2) {
  assert(b1->bitsize == b2->bitsize);
  return bvpoly_buffer_equal(&b1->exponent, &b2->exponent);
}


/*
 * Compute the common factors of b1->product and b2->product.
 * - both b1 and b2 must be normalized
 * - store the result in pbuffer
 * - pbuffer must be initialized
 * - the result is normalized
 */
void bvfactor_buffer_common_factors(pp_buffer_t *pbuffer, bvfactor_buffer_t *b1, bvfactor_buffer_t *b2) {
  assert(b1->bitsize == b2->bitsize);
  pp_buffer_copy(pbuffer, &b1->product);
  pp_buffer_gcd(pbuffer, &b2->product);
}


/*
 * Variant: compute the common factors of b1[0 ... n1-1] and b2[0 ... n2-1]
 * - all factor buffers must be normalized
 * - the result is stored in pbuffer
 */
void bvfactor_buffer_array_common_factors(pp_buffer_t *pbuffer, bvfactor_buffer_t *b1, uint32_t n1,
					  bvfactor_buffer_t *b2, uint32_t n2) {
  uint32_t i;

  assert(n1 > 0);

  pp_buffer_copy(pbuffer, &b1[0].product);
  for (i=1; i<n1; i++) {
    pp_buffer_gcd(pbuffer, &b1[i].product);
  }
  for (i=0; i<n2; i++) {
    pp_buffer_gcd(pbuffer, &b2[i].product);
  }
}


/*
 * Reduce: divide b->product by pbuffer
 * - pbuffer must be normalized and must be a divisor of b->product
 */
void bvfactor_buffer_reduce(bvfactor_buffer_t *b, pp_buffer_t *pbuffer) {
  pp_buffer_divide(&b->product, pbuffer);
}

/*
 * Divide b->product by x
 */
void bvfactor_buffer_reduce_by_var(bvfactor_buffer_t *b, int32_t x) {
  pp_buffer_divide_by_var(&b->product, x);
}



/*
 * Check whether b->product is linear (i.e., degree <= 1)
 * - b must be normalized
 */
bool bvfactor_buffer_is_linear(bvfactor_buffer_t *b) {
  return pp_buffer_is_trivial(&b->product);
}


/*
 * Check whether b->product is reduced to a single variable (i.e., degree = 1)
 * - b must be normalized
 */
bool bvfactor_buffer_is_var(bvfactor_buffer_t *b) {
  return b->product.len == 1 && b->product.prod[0].exp == 1;
}

/*
 * Get the variable of b->product if b->product has degree 1
 */
int32_t bvfactor_buffer_get_var(bvfactor_buffer_t *b) {
  assert(b->product.len == 1 && b->product.prod[0].exp == 1);
  return b->product.prod[0].var;
}


/*
 * Check whether the constant is zero
 * - b must be normalized
 */
bool bvfactor_buffer_is_zero(bvfactor_buffer_t *b) {
  uint32_t n;

  n = b->bitsize;
  assert(n > 0);
  if (n <= 64) {
    assert(b->constant64 == norm64(b->constant64, n));
    return b->constant64 == 0;
  } else {
    return bvconstant_is_zero(&b->constant);
  }
}
