/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * INTERVAL ARITHMETIC FOR SIGNED BITVECTORS
 */

#ifndef __BV64_INTERVAL_ABSTRACTION_H
#define __BV64_INTERVAL_ABSTRACTION_H

/*
 * Given an n-bit vector u = u[n-1] ... u[0], then we denote by
 * bv2int(u) the 2s-complement interpretation of u as an integer.
 *
 * We then have:
 *
 *  bv2int(u) = Sum i=0 to n-2 of 2^i u[i] - 2^(n-1) u[n-1]
 *
 *  u[n-1] is the sign bit.
 *
 * Without more information we can only conclude that
 *
 *   -2^(n-1) <= bv2int(u) <= 2^(n-1) - 1
 *
 * If we have more information, we can often get more precise bounds.
 * For example, if v has k bits and u is (sign-extend (n-k) v) then
 * all bits u[n-1] ... u[n-k] are equal and we get
 *
 *   -2^(k-1) <= bv2int(u) <= 2^(k-1) - 1
 *
 * This means that we could represent u using (k+1) bits without loss
 * of precision.
 *
 * In general, we want to reduce the size of arithmetic operation such
 * as bvadd and bvmul, by using k bits instead of n when that doesn't
 * lose precision. Given a polynomial p of n bits, we can compute the
 * number of significant bits in p. If that's less than n, then we can
 * convert p to (sign-extend k p') where p' is similar to p but with
 * smaller-size operations.
 *
 * To compute the number of significant bits in a bitvector term u, we
 * construct an abstraction:
 *
 *   alpha(u) = [k, s, low, highh]
 *
 * where
 * - k = number of significant bits in u (including the sign bit)
 * - s = sign bit
 * - low and high define an interval that contains bv2int(u).
 * - both low and high have k significant bits and k is between 1 and 64.
 *
 * Conversely, the concretization of [k, s, low, high] is the set of all
 * bitvectors u such that:
 * - u has k significant bits
 * - low <= u <= high
 * - u's sign bit is equal to s
 */


#include <assert.h>
#include <stdbool.h>
#include <stdint.h>


/*
 * Record to store the abstraction.
 */
typedef struct bv64_abs_s {
  uint32_t nbits;  // number of significant bits - 1
  int32_t  sign;   // sign bit
  int64_t low;     // lower bound
  int64_t high;    // upper bound
} bv64_abs_t;

/*
 * For the sign bit we use the same conventions as in the smt_core
 *  sign = null_literal (i.e., -1) means that the sign bit is unknown
 *  sign = true_literal (i.e.,  0) means that the sign bit is '1'
 *  sign = false_literal (i.e., 1) means that the sign bit is '0'
 * Otherwise
 *  sign = some non-negative integer l and we have not(l) = l^1
 */
enum {
  sign_undef = -1,
  sign_one = 0,  // i.e., true_literal
  sign_zero = 1, // i.e., false_literal
};

/*
 * Abstraction of a constant c.
 * - n = number of bits in c
 * - n must be positive and no more than 64
 */
extern void bv64_abs_constant(bv64_abs_t *a, uint64_t c, uint32_t n);


/*
 * Special cases: constants 0, +1, and -1
 */
extern void bv64_abs_zero(bv64_abs_t *a);
extern void bv64_abs_one(bv64_abs_t *a);
extern void bv64_abs_minus_one(bv64_abs_t *a);


/*
 * Full interval for bitvectors of n bits
 * - the sign is set to undef
 */
extern void bv64_abs_default(bv64_abs_t *a, uint32_t n);


/*
 * Checks whether a is more precise than the full interval of n bits
 * - this returns true if a->nbits < n or a->low > 2^(n-1) or 
 *   a->high < 2^(n-1)-1 or a->sign != undef
 */
extern bool bv64_abs_nontrivial(bv64_abs_t *a, uint32_t n);

// converse
static inline bool bv64_abs_trivial(bv64_abs_t *a, uint32_t n) {
  return !bv64_abs_nontrivial(a, n);
}


/*
 * Abstraction of an array u of n bits.
 * - n must be positive and no more thant 64
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
extern void bv64_abs_array(bv64_abs_t *a, int32_t zero, const int32_t *u, uint32_t n);


/*
 * Abstraction for (- a): 
 * - the result is stored in place
 */
extern void bv64_abs_negate(bv64_abs_t *a);

/*
 * Abstraction for a * c where c is a constant
 * - n = number of bits in c
 */
extern void bv64_abs_mul_const(bv64_abs_t *a, uint64_t c, uint32_t n);

/*
 * Abstraction for binary operations: (a + b), (a - b), (a * b), (a ^ d)
 * - the result is stored in a
 */
extern void bv64_abs_add(bv64_abs_t *a, const bv64_abs_t *b);
extern void bv64_abs_sub(bv64_abs_t *a, const bv64_abs_t *b);
extern void bv64_abs_mul(bv64_abs_t *a, const bv64_abs_t *b);
extern void bv64_abs_power(bv64_abs_t *a, uint32_t d);


#endif /* __BV64_INTERVAL_ABSTRACTION_H */
