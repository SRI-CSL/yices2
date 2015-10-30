/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>

#include "terms/bv64_constants.h"
#include "terms/bv64_sign_abstraction.h"
#include "utils/int_powers.h"


/*
 * For debugging: check whether a is consistent
 */
#ifndef NDEBUG
static bool bv64_abs_consistent(bv64_abs_t *a) {
  uint32_t k;

  k = a->nbits;
  if (k == 0) {
    return a->low == 0 && a->high == 0;
  } else {
    // low <= high and both must be normalized modulo 2^k
    return a->low <= a->high && a->low == norm64(a->low, k) && a->high == norm64(a->high, k);
  }
}
#endif

/*
 * Abstraction of a constant c.
 * - n = number of bits in c
 * - n must be positive and no more than 64
 */
void bv64_abs_constant(bv64_abs_t *a, uint64_t c, uint32_t n) {
  uint32_t k;

  assert(1 <= n && n <= 64);

  k = n - 1;

  if (tst_bit64(c, k)) {
    // the sign bit is one
    while (k > 0 && tst_bit64(c, k - 1)) {
      k --;
    }
    a->nbits = k;
    a->sign = sign_one;
  } else {
    // the sign bit is zero
    while (k > 0 && !tst_bit64(c, k-1)) {
      k --;
    }
    a->nbits = k;
    a->sign = sign_zero;
  }

  if (k == 0) {
    a->low = 0;
    a->high = 0;
  } else {
    a->low = norm64(c, k);
    a->high = norm64(c, k);
  }

  assert(bv64_abs_consistent(a));
}


/*
 * Special cases: constant 0, +1, and -1
 */
void bv64_abs_zero(bv64_abs_t *a) {
  a->nbits = 0;
  a->sign = sign_zero;
  a->low = 0;
  a->high = 0;

  assert(bv64_abs_consistent(a));
}

void bv64_abs_one(bv64_abs_t *a) {
  a->nbits = 1;
  a->sign = sign_zero;
  a->low = 1;
  a->high = 1;

  assert(bv64_abs_consistent(a));
}

void bv64_abs_minus_one(bv64_abs_t *a) {
  a->nbits = 0;
  a->sign = sign_one;
  a->low = 0;
  a->high = 0;

  assert(bv64_abs_consistent(a));
}


/*
 * Abstraction of an array u of n bits.
 * - n must be positive and no more than 64
 *
 * We want this to work for both arrays of Boolean terms and arrays of
 * literals.  Terms and literals use the same conventions:
 * - they are represented by signed 32bit integers
 * - the null term or literal is denoted by -1
 * - negating a term or a literal corresponds to flipping the least
 *   significant bit of the index.
 * The only difference between terms and literals is the encoding of
 * true and false: 
 * - true_term = 2 and true_literal = 0
 * - false_term = 3 and false_literal = 
 *
 * To deal with both cases, this function takes an extra parameter:
 * zero, which must be the encoding of false.
 */
void bv64_abs_array(bv64_abs_t *a, int32_t zero, const int32_t *u, uint32_t n) {
  uint32_t i, k;
  int32_t s, one;

  assert(1 <= n && n <= 64 && zero >= 0);

  one = negate_sign(zero);

  k = n-1;
  s = u[k];
  while (k > 0 && u[k-1] == s) {
    k --;
  }

  a->nbits = k;
  if (s == zero) {
    a->sign = sign_zero;
  } else if (s == one) {
    a->sign = sign_one;
  } else {
    a->sign = s;
  }

  if (k == 0) {
    a->low = 0;
    a->high = 0;
  } else {
    a->low = 0;
    a->high = mask64(k); // all bits sets to 1

    for (i=0; i<k; i++) {
      if (u[i] == zero) {
	clr_bit64(a->high, i);
      } else if (u[i] == one) {
	set_bit64(a->low, i);
      }
    }
  }

  assert(bv64_abs_consistent(a));  
}


