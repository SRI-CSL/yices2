/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * OPERATIONS ON SMALL BITVECTOR CONSTANTS
 */

/*
 * A bitvector of size <= 64 can be stored compactly in a 64bit
 * unsigned integer.  The following operations normalize and
 * manipulate bit vector constants in this representation.
 *
 * The data structures defined in bv_constants.h can be used
 * for bitvector constants of larger sizes.
 */

#ifndef __BV64_CONSTANTS_H
#define __BV64_CONSTANTS_H

#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <assert.h>

#include "terms/rationals.h"


/*
 * Mask for normalizing an n-bit constant where 0 < n <= 64
 * - x & mask64(n) is the normalization of x
 *   (i.e., high-order bits are 0)
 * - warning: shift by 64 is undefined in C
 */
static inline uint64_t mask64(uint32_t n) {
  assert(0 < n && n <= 64);
  return (~((uint64_t) 0)) >> (64 - n);
}


/*
 * Normalize c modulo 2^n (set high-order bits to 0)
 */
static inline uint64_t norm64(uint64_t c, uint32_t n) {
  assert(0 < n && n <= 64);
  return c & mask64(n);
}


/*
 * Check whether c is equal to -1 modulo 2^n
 */
static inline bool bvconst64_is_minus_one(uint64_t c, uint32_t n) {
  assert(0 < n && n <= 64);
  return (c & mask64(n)) == mask64(n);
}


/*
 * Mask to select the sign bit in an n-bit number
 */
static inline uint64_t sgn_bit_mask64(uint32_t n) {
  assert(0 < n && n <= 64);
  return ((uint64_t) 1) << (n - 1);
}


/*
 * Test whether bit k of c is 1 or 0
 * - true means 1, false means 0
 */
static inline bool tst_bit64(uint64_t c, uint32_t k) {
  assert(0 <= k && k < 64);
  return c & (((uint64_t) 1) << k);
}


/*
 * Clear or set bit k of c
 */
static inline uint64_t clr_bit64(uint64_t c, uint32_t k) {
  assert(0 <= k && k < 64);
  return c & ~(((uint64_t) 1) << k);
}

static inline uint64_t set_bit64(uint64_t c, uint32_t k) {
  assert(0 <= k && k < 64);
  return c | (((uint64_t) 1) << k);
}


/*
 * Get the sign bit of c, interpreted as an n-bit 2s-complement
 * number.
 */
static inline bool tst_sign_bit64(uint64_t c, uint32_t n) {
  assert(0 < n && n <= 64);
  return tst_bit64(c, n-1);
}

static inline bool is_neg64(uint64_t c, uint32_t n) {
  return tst_sign_bit64(c, n);
}

static inline bool is_pos64(uint64_t c, uint32_t n) {
  return ! tst_sign_bit64(c, n);
}


/*
 * Maximal and minimal n-bit signed number
 */
static inline uint64_t max_signed64(uint32_t n) {
  assert(0 < n && n <= 64);
  return (n == 1) ? 0 : mask64(n-1); // all bits 1, except the sign bit
}

static inline uint64_t min_signed64(uint32_t n) {
  return sgn_bit_mask64(n); // all bits 0, except the sign bit
}



/*
 * Arithmetic and logical shift
 */

/*
 * Shift left: (a << b), padding with 0.
 * - n = number of bits in a and b
 * - if b is more than n, this returns 0b00000
 * - the result is normalized
 */
extern uint64_t bvconst64_lshl(uint64_t a, uint64_t b, uint32_t n);


/*
 * Logical shift right: (a >> b), padding with 0
 * - n = number of bits in a and b
 * - if b is more than n, return 0b00000
 * - the result is normalized.
 */
extern uint64_t bvconst64_lshr(uint64_t a, uint64_t b, uint32_t n);


/*
 * Arithmetic shift right: (a >> b), padding with a's sign bit
 * - n = number of bits in a and b
 * - if b is more than n, return 0b00000 or 0b11111 depending on a's sign bit
 * - the result is normalized.
 */
extern uint64_t bvconst64_ashr(uint64_t a, uint64_t b, uint32_t n);



/*
 * Operations on constants interpreted as n-bit 2's complement numbers.
 */

/*
 * Convert c into a signed 64 bit number
 */
extern int64_t signed_int64(uint64_t c, uint32_t n);


/*
 * Check whether a >= b: both are interpreted as n-bit signed numbers
 */
extern bool signed64_ge(uint64_t a, uint64_t b, uint32_t n);


/*
 * Check whether a>b: both are interpreted as n-bit signed numbers
 */
extern bool signed64_gt(uint64_t a, uint64_t b, uint32_t n);


/*
 * Variants: a <= b and a < b
 */
static inline bool signed64_le(uint64_t a, uint64_t b, uint32_t n) {
  return signed64_ge(b, a, n);
}

static inline bool signed64_lt(uint64_t a, uint64_t b, uint32_t n) {
  return signed64_gt(b, a, n);
}



/*
 * DIVISIONS
 *
 * These are the quotient and remainder operations defined in the SMT-LIB notation.
 * They are identical to the usual division and remainder operation, except that a
 * zero divider is allowed.
 *
 * All operations compute the quotient or remainder in the division of x by y.
 * Both x and y must be normalized modulo 2^n, and the result is also normalized
 * modulo 2^n,
 *
 * Unsigned division: x and y are interpreted as unsigned n-bit numbers
 *   bvconst64_udiv2z(x, y, n): quotient
 *   bvconst64_urem2z(x, y, n): remainder
 *
 * Signed division: x and y are interpreted as 2's complement n-bit numbers
 * (This is 'truncated division' with rounding toward 0)
 *   bvconst64_sdiv2z(x, y, n): quotient in signed division
 *   bvconst64_srem2z(x, y, n): remainder in signed division
 *
 * Floor division: x and y are interpreted as 2's complement n-bit number.
 * Rounding is toward minus infinity.
 *   bcconst64_smod2z(x, y, n): remainder
 *
 * Properties:
 *   a1 = a2 * (udiv a1 a2)  + (urem a1 a2)
 *   a1 = a2 * (sdiv a1 a2)  + (srem a1 a2)
 *   a1 = a2 * (floor a1/a2) + (smod a1 a2)
 *   (sdiv a1 a2) has the same sign as a1/a2
 *   (srem a1 a2) has the same sign as a1
 *   (smod a1 a2) has the same sign as a2
 *
 * For division by 0, we use the following rules:
 *   (udiv a 0) = 0b11...1
 *   (urem a 0) = a
 *   (sdiv a 0) = 0b111..1 if a >= 0
 *   (sdiv a 0) = 0b00..01 if a < 0
 *   (srem a 0) = a
 *   (smod a 0) = a
 */
extern uint64_t bvconst64_udiv2z(uint64_t x, uint64_t y, uint32_t n);
extern uint64_t bvconst64_urem2z(uint64_t x, uint64_t y, uint32_t n);
extern uint64_t bvconst64_sdiv2z(uint64_t x, uint64_t y, uint32_t n);
extern uint64_t bvconst64_srem2z(uint64_t x, uint64_t y, uint32_t n);
extern uint64_t bvconst64_smod2z(uint64_t x, uint64_t y, uint32_t n);



/*
 * Convert a string of '0's and '1's to a constant
 * - n = number of bits (n must be between 1 and 64)
 * - s must be at least n character long.
 *
 * Read the first n characters of s. All must be '0' and '1'
 * - the string is interpreted as a big-endian format: the
 *   first character is the high order bit.
 *
 * If the string format is wrong, return -1 and leave *a unchanged.
 * Otherwise, return 0 and store the result in *a (normalized modulo 2^n).
 */
extern int32_t bvconst64_set_from_string(uint64_t *a, uint32_t n, char *s);


/*
 * Convert a string interpreted as an hexadecimal number to a constant.
 * - n = number of characters to read (n must be between 1 and 16)
 * - s must be at least n character long.
 *
 * Read the first n characters of s.
 * All must be in the ranges '0' to '9' or 'a' to 'f' or 'A' to 'F'.
 * The string is read in big-endian format: first character defines
 * the four high-order bits.
 *
 * Return -1 if the format is wrong (and leave *a unchanged).
 * Return 0 otherwise and store the result in a, normalized modulo 2^4n.
 */
extern int32_t bvconst64_set_from_hexa_string(uint64_t *a, uint32_t n, char *s);


/*
 * Convert the n low-order bits of a rational q to a bitvector
 * constant of n-bits
 * - q must be an integer
 */
extern uint64_t bvconst64_from_q(uint32_t n, rational_t *q);


/*
 * Display a in binary format. n = number of bits
 */
extern void bvconst64_print(FILE *f, uint64_t a, uint32_t n);


#endif /* __BV64_CONSTANTS_H */
