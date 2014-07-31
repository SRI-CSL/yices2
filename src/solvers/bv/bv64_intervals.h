/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * INTERVALS OF BIT-VECTOR VALUES (1 to 64 bits)
 */

/*
 * For simplifying bitvector constraints: we compute the lower/upper bounds
 * on bitvector variables. A pair lower/upper bounds is stored in an
 * interval record. This module provides operations on intervals
 * intended for bitvectors of no more than 64bits.
 */

#ifndef __BV64_INTERVALS_H
#define __BV64_INTERVALS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "terms/bv64_constants.h"


/*
 * Interval structure:
 * - low, high = two bounds
 * - nbits = number of bits in low and high (nbits must be between 1 and 64)
 * - if bitsize = n then both low and high are normalized modulo 2^n
 * - there are two possible interpretations depending on whether
 *   the bounds are seen as signed or unsigned integers
 */
typedef struct bv64_interval_s {
  uint64_t low;
  uint64_t high;
  uint32_t nbits;
} bv64_interval_t;



/*
 * Initialize intv to [x, x]
 * - x must be normalized modulo 2^n
 */
static inline void bv64_point_interval(bv64_interval_t *intv, uint64_t x, uint32_t n) {
  assert(1 <= n && n <= 64 && x == norm64(x, n));
  intv->low = x;
  intv->high = x;
  intv->nbits = n;
}


/*
 * Initialize to the interval [0, 0]
 */
static inline void bv64_zero_interval(bv64_interval_t *intv, uint32_t n) {
  assert(1 <= n && n <= 64);
  intv->low = 0;
  intv->high = 0;
  intv->nbits = n;
}


/*
 * Initialize to [x, y] (unsigned)
 * - x and y must be normalized modulo 2^n
 * - x <= y must hold
 */
static inline void bv64_interval_set_u(bv64_interval_t *intv, uint64_t x, uint64_t y, uint32_t n) {
  assert(1 <= n && n <= 64 && x == norm64(x, n) && y == norm64(y, n) && x <= y);
  intv->low = x;
  intv->high = y;
  intv->nbits = n;
}


/*
 * Initialize to [x, y] (signed)
 * - x and y must be normalized modulo 2^n
 * - x <= y must hold
 */
static inline void bv64_interval_set_s(bv64_interval_t *intv, uint64_t x, uint64_t y, uint32_t n) {
  assert(1 <= n && n <= 64 && x == norm64(x, n) && y == norm64(y, n) && signed64_le(x, y, n));
  intv->low = x;
  intv->high = y;
  intv->nbits = n;
}


/*
 * Initialize to the trivial unsigned interval:
 * - low = 0, high = 2^n-1
 */
static inline void bv64_triv_interval_u(bv64_interval_t *intv, uint32_t n) {
  assert(1 <= n && n <= 64);
  intv->low = 0;
  intv->high = mask64(n);
  intv->nbits = n;
}


/*
 * Initialize to the trivial signed interval:
 * - low = -2^(n-1), high = 2^(n-1) - 1
 */
static inline void bv64_triv_interval_s(bv64_interval_t *intv, uint32_t n) {
  assert(1 <= n && n <= 64);
  intv->low = min_signed64(n);
  intv->high = max_signed64(n);
  intv->nbits = n;
}


/*
 * Check whether the bounds are normalized
 */
static inline bool bv64_interval_is_normalized(bv64_interval_t *intv) {
  return intv->low == norm64(intv->low, intv->nbits)
    && intv->high == norm64(intv->high, intv->nbits);
}


/*
 * Check whether the interval is trivial (i.e., contains every n-bit bitvectors)
 * - two versions: signed/unsigned
 */
static inline bool bv64_interval_is_triv_u(bv64_interval_t *intv) {
  assert(bv64_interval_is_normalized(intv));
  return intv->low == 0 && intv->high == mask64(intv->nbits);
}

static inline bool bv64_interval_is_triv_s(bv64_interval_t *intv) {
  assert(bv64_interval_is_normalized(intv));
  return intv->low == min_signed64(intv->nbits) && intv->high == max_signed64(intv->nbits);
}


/*
 * Compute the best overapproximation of [a.low + b.low, a.high + b.high] modulo 2^n
 * - n = bitsize of a and b
 * - a and b must have the same bitsize and be normalized
 * - the result is stored in a
 *
 * For the unsigned version, there's loss of precision if
 *   (a.low + b.low < 2^n <= a.high + b.high).
 * In this case, the result is set to [0, 2^n-1]
 *
 * For the signed version, there's loss of precision if either
 *     a.low + b.low underflows but not a.high + b.high
 * or  a.low + b.low does not overflow, but a.high + b.high does
 * In either case, the result is set to [0b10000, 0b01111] (trivial interval)
 */
extern void bv64_interval_add_u(bv64_interval_t *a, bv64_interval_t *b);
extern void bv64_interval_add_s(bv64_interval_t *a, bv64_interval_t *b);


/*
 * Same thing for [a.low - b.high, a.high - b.low] modulo 2^n
 * - a and b must have the same bit size and be normalized
 * - the result is stored in a
 * - the functions detect overflow/underflow and set a to the
 *   trivial interval if necessary
 */
extern void bv64_interval_sub_u(bv64_interval_t *a, bv64_interval_t *b);
extern void bv64_interval_sub_s(bv64_interval_t *a, bv64_interval_t *b);


/*
 * Approximation of [a.low + c * b.low, a.high + c * b.high] modulo 2^n
 * - a and b must have the same bitsize and be normalized
 * - c must be normalized modulo 2^n too
 * - the result is stored in a
 * This gives a precise result only if the constant c is small (in absolute value)
 * and the intervals a and b are small too.
 */
extern void bv64_interval_addmul_u(bv64_interval_t *a, bv64_interval_t *b, uint64_t c);
extern void bv64_interval_addmul_s(bv64_interval_t *a, bv64_interval_t *b, uint64_t c);



#endif /* __BV64_INTERVALS_H */
