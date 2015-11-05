/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>

#include "terms/bv64_constants.h"
#include "terms/bv64_interval_abstraction.h"
#include "utils/int_powers.h"

#ifndef NDEBUG
/*
 * Number of significant bits in x
 * - if the result is k then -2^(k-1) <= x < 2^(k-1)
 */
static uint32_t num_significant_bits(int64_t x) {
  int64_t low, high;
  uint32_t k;

  low = INT64_MIN/2;
  high = -low;
  k = 64;
  while (low <= x && x < high) {
    low /= 2;
    high /= 2;
    k --;
  }
  return k;
}

static bool bv64_consistent_sign(bv64_abs_t *a) {
  if (a->low >= 0) {
    return a->sign == sign_zero;
  } else if (a->high < 0) {
    return a->sign == sign_one;
  } else {
    return true;
  }
}

static bool bv64_consistent_nbits(bv64_abs_t *a) {
  uint32_t k, lk, hk;

  k = a->nbits;
  lk = num_significant_bits(a->low);
  assert(1 <= lk && lk <= 64);
  hk = num_significant_bits(a->high);
  assert(1 <= lk && lk <= 64);

  return (k == lk && k >= hk) || (k == hk && k >= lk);
}

static bool bv64_abs_consistent(bv64_abs_t *a) {
  return bv64_consistent_sign(a) && bv64_consistent_nbits(a);
}
#endif


/*
 * Abstraction of a constant c.
 * - n = number of bits in c
 * - n must be positive and no more than 64
 */
void bv64_abs_constant(bv64_abs_t *a, uint64_t c, uint32_t n) {
  int64_t sc;
  uint32_t k;

  assert(1 <= n && n <= 64);

  k = n - 1;

  if (tst_bit64(c, k)) {
    // the sign bit is one
    while (k > 0 && tst_bit64(c, k - 1)) {
      k --;
    }
    a->nbits = k + 1;
    a->sign = sign_one;
    sc = (int64_t) (c | ~mask64(n)); // sign extend
    a->low = sc;
    a->high = sc;
  } else {
    // the sign bit is zero
    while (k > 0 && !tst_bit64(c, k-1)) {
      k --;
    }
    a->nbits = k + 1;
    a->sign = sign_zero;
    sc = (int64_t) c;
    a->low = sc;
    a->high = sc;
  }

  assert(bv64_abs_consistent(a));
}


/*
 * Special cases: constant 0, +1, and -1
 */
void bv64_abs_zero(bv64_abs_t *a) {
  a->nbits = 1;
  a->sign = sign_zero;
  a->low = 0;
  a->high = 0;

  assert(bv64_abs_consistent(a));
}

void bv64_abs_one(bv64_abs_t *a) {
  a->nbits = 2;
  a->sign = sign_zero;
  a->low = 1;
  a->high = 1;

  assert(bv64_abs_consistent(a));
}

void bv64_abs_minus_one(bv64_abs_t *a) {
  a->nbits = 1;
  a->sign = sign_one;
  a->low = -1;
  a->high = -1;

  assert(bv64_abs_consistent(a));
}


/*
 * Least precise interval
 */
static void bv64_top_abs(bv64_abs_t *a) {
  a->nbits = 64;
  a->sign = sign_undef;
  a->low = INT64_MIN;
  a->high = INT64_MAX;

  assert(bv64_abs_consistent(a));
}


/*
 * Flip sign
 */
static inline int32_t negate_sign(int32_t s) {
  assert(s >= 0);
  return s ^ 1;
}

// build 2^k
static inline int64_t power2(uint32_t k) {
  assert(k <= 63);
  return (int64_t)(((uint64_t) 1) << k);
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
 * - false_term = 3 and false_literal = 1
 *
 * To deal with both cases, this function takes an extra parameter:
 * zero, which must be the encoding of false.
 */
void bv64_abs_array(bv64_abs_t *a, int32_t zero, const int32_t *u, uint32_t n) {
  uint32_t i, k;
  int32_t s, one;
  uint64_t lb, ub;
  int64_t s_min, s_max;

  assert(1 <= n && n <= 64 && zero >= 0);

  one = negate_sign(zero);

  k = n-1;
  s = u[k];
  while (k > 0 && u[k-1] == s) {
    k --;
  }

  a->nbits = k + 1;
  if (s == zero) {
    a->sign = sign_zero;
  } else if (s == one) {
    a->sign = sign_one;
  } else {
    a->sign = s;
  }

  /*
   * Upper and lower bounds on u:
   * - u = -2^k s + 2^(k-1) * u[k-1] + ... + 2 * u[1] + u[0]
   * - we use s_min <= -2^k <= s_max
   *   and lb <= 2^(k-1) * u[k-1] + ... + 2 * u[1] + u[0]
   */
  assert(k <= 63);

  s_min = - power2(k); // -2^k
  s_max = 0;
  if (s == zero) {
    s_min = s_max; // both are 0
  } else if (s == one) {
    s_max = s_min; // both are -2^k
  }

  if (k == 0) {
    lb = 0;
    ub = 0;
  } else {
    lb = 0;
    ub = mask64(k); // all bits set to 1
    for (i=0; i<k; i++) {
      if (u[i] == zero) {
	ub = clr_bit64(ub, i);
      } else if (u[i] == one) {
	lb = set_bit64(lb, i);
      }
    }
  }

  assert(lb <= ub && ub <= ((uint64_t) INT64_MAX));

  a->low = s_min + (int64_t) lb;
  a->high = s_max + (int64_t) ub;

  assert(bv64_abs_consistent(a));  
}


/*
 * Abstraction for (- a): 
 * - the result is stored in place
 */
void bv64_abs_negate(bv64_abs_t *a) {
  uint32_t k;

  k = a->nbits;

  assert(1 <= k && k <= 64);

  if (a->low == - power2(k-1)) {
    // - a->low does not fit on k bits (it's 2^(k-1))
    k ++;
    if (k > 64) {
      bv64_top_abs(a);
      return;
    }
  } 

  a->nbits = k;
  a->low = - a->high;
  a->high = a->low;
  if (a->low >= 0) {
    a->sign = sign_zero;
  } else if (a->high < 0) {
    a->sign = sign_one;
  } else {
    // the new interval [-high, -low] contains 0 so we've lost
    // the sign information (even if we knew the sign of a).
    a->sign = sign_undef;
  }

  assert(bv64_abs_consistent(a));
}


/*
 * Abstraction for binary operations: (a + b), (a - b), (a * b), (a ^ d)
 * - the result is stored in a
 */
void bv64_abs_add(bv64_abs_t *a, const bv64_abs_t *b) {
}

void bv64_abs_sub(bv64_abs_t *a, const bv64_abs_t *b) {
}

void bv64_abs_mul(bv64_abs_t *a, const bv64_abs_t *b) {
}

void bv64_abs_power(bv64_abs_t *a, uint32_t d) {
}

