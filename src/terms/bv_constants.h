/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Bit-vector constants = finite-precision integers.
 *
 * Constants are represented as fixed-size arrays of integers.
 * This should be more efficient than gmp numbers for typical
 * bit vector size (e.g., 32, 64 bits).
 *
 * A bitvector constant is stored as an array of k words (k > 0).
 * Each word is an unsigned 32 bit integer.
 * - word[0] = least significant word
 * - word[k-1] = most significant word
 *
 * All arithmetic operations are done on full arrays of 32k bits.
 * For a constant of n bits, the value modulo (2^n) is obtained by
 * calling normalize, which clears the 32k - n high-order bits of bv,
 * where k = ceil(n/32).
 *
 * Bitvector constants can be allocated via the bvconst_alloc
 * function. This requires the user to remember the wordsize of the
 * constant. Alternatively, one can use a resizable buffer
 * (bvconstant_s structure).
 */

#ifndef __BV_CONSTANTS_H
#define __BV_CONSTANTS_H

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include <gmp.h>

#include "terms/rationals.h"



/*******************************
 *  ALLOCATION OF WORD ARRAYS  *
 ******************************/

/*
 * The module maintains an global store for allocation
 * of bitvector constants of different sizes. The following
 * functions must be used to allocate/free vectors in
 * that global store.
 */

/*
 * Initialize the internal store. This must be called first,
 * before any call to bvconst_alloc.
 */
extern void init_bvconstants(void);

/*
 * Cleanup: free all memory used by the module
 */
extern void cleanup_bvconstants(void);

/*
 * Allocation of a constant of k words. It's not initialized.
 */
extern uint32_t *bvconst_alloc(uint32_t k);

/*
 * Free an allocated constant bv of k words.
 * - bv must be the result of a call to bvconst_alloc(k).
 */
extern void bvconst_free(uint32_t *bv, uint32_t k);



/****************************************
 * OPERATIONS ON BVCONSTANT STRUCTURES  *
 ***************************************/

/*
 * bvconstant: a bitsize + a pointer to an array of words
 * - each word is 32bit.
 * - the array is extended as needed.
 */
typedef struct bvconstant_s {
  uint32_t *data;     // the array itself.
  uint32_t bitsize;   // number of bits
  uint32_t width;     // ceil(number of bits/32)
  uint32_t arraysize; // size of the array
} bvconstant_t;


/*
 * Initialization: bitsize is set to 0
 */
extern void init_bvconstant(bvconstant_t *b);

/*
 * Delete: free allocated memory
 */
extern void delete_bvconstant(bvconstant_t *b);

/*
 * Resize: make the array large enough for n bits
 */
extern void bvconstant_set_bitsize(bvconstant_t *b, uint32_t n);

/*
 * Resize and initialize to all bits to 0 or one (and normalize).
 */
extern void bvconstant_set_all_zero(bvconstant_t *b, uint32_t n);
extern void bvconstant_set_all_one(bvconstant_t *b, uint32_t n);


/*
 * Resize and initialize with a (and normalize).
 * - n = number of bits
 */
extern void bvconstant_copy(bvconstant_t *b, uint32_t n, const uint32_t *a);


/*
 * Variant: initialize with a 64bit constant a, and normalize.
 * - n = number of bits
 */
extern void bvconstant_copy64(bvconstant_t *b, uint32_t n, uint64_t a);



/*******************************
 *  OPERATIONS ON WORD ARRAYS  *
 ******************************/

/*
 * Normalize bv modulo 2^n: set to 0 all the high-order bits
 * of bv[k-1], where k = ceil(n/32).
 */
extern void bvconst_normalize(uint32_t *bv, uint32_t n);


/*
 * Check whether bv is normalized modulo 2^n (i.e., whether the high
 * order bits are 0).
 */
extern bool bvconst_is_normalized(const uint32_t *bv, uint32_t n);



/*
 * Hash code of bitvector constant a, n = bitsize
 * - a must be normalized modulo 2^n first.
 */
extern uint32_t bvconst_hash(const uint32_t *a, uint32_t n);


/*
 * Display bv in binary format: 0b.....
 */
extern void bvconst_print(FILE *f, const uint32_t *bv, uint32_t n);


/*
 * bit operations. If bv has size k, then i must be between 0 and 32k-1.
 */
extern bool bvconst_tst_bit(const uint32_t *bv, uint32_t i);
extern void bvconst_set_bit(uint32_t *bv, uint32_t i);
extern void bvconst_clr_bit(uint32_t *bv, uint32_t i);
extern void bvconst_flip_bit(uint32_t *bv, uint32_t i);
extern void bvconst_assign_bit(uint32_t *bv, uint32_t i, bool bit);


/*
 * Assignment to array bv of k words.
 * - clear:     bv := 0b000...000
 * - set_one:   bv := 0b000...001
 * - set_minus_one:   bv := 0b111...111
 * - set32:     bv := a padded with zeros (a is 32bits)
 * - set64:     same thing (a is 64 bits)
 * - set32_signed:  bv := sign_extend of a
 * - set64_signed:  same thing for a 64bit integer a
 * - set_mpz:   assign 32k low-order bits of z (padded with 0)
 *              z must be non-negative
 * - set_q:     same thing
 * - set:       copy a into b
 * - set_array: initialize bv from an array of n integers
 *              bit i of bv = 0 if a[i] == 0,
 *              bit i of bv = 1 if a[i] != 0
 */
extern void bvconst_clear(uint32_t *bv, uint32_t k);
extern void bvconst_set_one(uint32_t *bv, uint32_t k);
extern void bvconst_set_minus_one(uint32_t *bv, uint32_t k);
extern void bvconst_set32(uint32_t *bv, uint32_t k, uint32_t a);
extern void bvconst_set64(uint32_t *bv, uint32_t k, uint64_t a);
extern void bvconst_set32_signed(uint32_t *bv, uint32_t k, int32_t a);
extern void bvconst_set64_signed(uint32_t *bv, uint32_t k, int64_t a);
extern void bvconst_set_mpz(uint32_t *bv, uint32_t k, const mpz_t z);
extern void bvconst_set_q(uint32_t *bv, uint32_t k, rational_t *r);

extern void bvconst_set(uint32_t *bv, uint32_t k, const uint32_t *a);
extern void bvconst_set_array(uint32_t *bv, const int32_t *a, uint32_t n);


/*
 * Other constant assignments: n = number of bits
 * - set_min_signed:  bv := 0b100...000
 * - set_max_signed:  bv := 0b011...111
 * - bv must be large enough (at least ceil(n/32) words)
 * - bv is normalized
 */
extern void bvconst_set_min_signed(uint32_t *bv, uint32_t n);
extern void bvconst_set_max_signed(uint32_t *bv, uint32_t n);


/*
 * Assignment + extension
 * b: n-bit vector, a: m-bit vector with 0 < m <= n
 * assign a to b with padding as defined by mode:
 * - mode = 0: padding with 0
 * - mode = 1: padding with 1
 * - mode = -1: sign extension (padding = high-order bit).
 */
extern void bvconst_set_extend(uint32_t *bv, uint32_t n, const uint32_t *a,
                               uint32_t m, int32_t mode);


/*
 * Convert a string of '0' and '1's to a bitvector constant.
 * - n = number of bits, must be positive.
 * - s must be at least n character long
 *
 * Reads the n first characters of s. All must be '0' or '1'
 * - the string is assumed in big-endian format: the
 *   first character is the high-order bit.
 *
 * Return code: -1 if the string format is wrong, 0 otherwise.
 */
extern int32_t bvconst_set_from_string(uint32_t *bv, uint32_t n, const char *s);


/*
 * Convert a string, interpreted as hexadecimal digits,
 * to a bitvector constant.
 * - n = number of characters, must be positive.
 * - s must be at least n character long
 * - bv must be an array of at least ceil(4*n/32) words
 *
 * Reads the n first characters of s.
 * All must be '0' to '9' or 'a' to 'f' or 'A' to 'F'
 * - the string is assumed in big-endian format: the
 *   first character defines the high-order 4 bits.
 *
 * Return code: -1 if the string format is wrong, 0 otherwise.
 */
extern int32_t bvconst_set_from_hexa_string(uint32_t *bv, uint32_t n, const char *s);


/*
 * Store the n lowest order bits of bv into a
 * - as an integer array: a[i] = bit i of bv (either 0 or 1)
 * - n must be no more than bv's bit width
 */
extern void bvconst_get_array(const uint32_t *bv, int32_t *a, uint32_t n);


/*
 * Convert bv to an GMP integer.
 * - k = size of bv in words.
 * - as an mpz integer
 * - bv should be normalized first
 */
extern void bvconst_get_mpz(const uint32_t *bv, uint32_t k, mpz_t z);


/*
 * Get the 32 or 64 low-order bits of bv
 * - as a 32bit integer
 * - as a 64bit integer (bv must be more than 32bits).
 */
static inline uint32_t bvconst_get32(const uint32_t *bv) {
  return *bv;
}

static inline uint64_t bvconst_get64(const uint32_t *bv) {
  return ((uint64_t) bv[0]) | (((uint64_t) bv[1]) << 32);
}


/*
 * Population count: number of 1 bits in bv
 * - bv must be normalized
 * - k must be the size of bv in words
 */
extern uint32_t bvconst_popcount(const uint32_t *bv, uint32_t k);



/*
 * Bitwise operations: bv and a must be of size k
 * - result is in bv
 */
extern void bvconst_complement(uint32_t *bv, uint32_t k);
extern void bvconst_and(uint32_t *bv, uint32_t k, uint32_t *a);
extern void bvconst_or(uint32_t *bv, uint32_t k, uint32_t *a);
extern void bvconst_xor(uint32_t *bv, uint32_t k, uint32_t *a);


/*
 * In-place shifts:
 * n = size of bv (number of bits)
 * m = shift amount = integer between 0 and n
 * b = padding bit = either 0 or 1
 */
extern void bvconst_shift_left(uint32_t *bv, uint32_t n, uint32_t m, bool b);
extern void bvconst_shift_right(uint32_t *bv, uint32_t n, uint32_t m, bool b);


/*
 * More shift operations:
 * - a is shifted by the amount defined by b
 * - the result is stored in *bv and normalized
 * - n = number of bits in a, b, and bv
 *
 * Operations:
 * - lshl: logical shift left
 * - lshr: logical shift right
 * - ashr: arithmetic shift right
 */
extern void bvconst_lshl(uint32_t *bv, uint32_t *a, uint32_t *b, uint32_t n);
extern void bvconst_lshr(uint32_t *bv, uint32_t *a, uint32_t *b, uint32_t n);
extern void bvconst_ashr(uint32_t *bv, uint32_t *a, uint32_t *b, uint32_t n);



/*
 * Extraction: store bits[l..(h-1)] of a into bv[0..(h-l-1)]
 */
extern void bvconst_extract(uint32_t *bv, uint32_t *a, uint32_t l, uint32_t h);


/*
 * Concatenation: bv[0...n-1] = a[0.. n-1] and bv[n ... n+m-1] = b[0...m-1]
 */
extern void bvconst_concat(uint32_t *bv, uint32_t *a, uint32_t n, uint32_t *b, uint32_t m);


/*
 * Arithmetic operations:
 *  k = size of operands in number of words (= size of bv, a a1, a2)
 *  all operations are done modulo 2^(32k).
 *  the result is in bv
 *  a, a1, and a2 must not overlap with bv
 * - negate:  bv := - bv
 * - add_one: bv := bv + 1
 * - sub_one: bv := bv - 1
 * - add:     bv += a
 * - sub:     bv -= a
 * - mul:     bv *= a
 * - addmul:  bv += a1 * a2
 * - submul:  bv -= a1 * a2
 *
 * - negate2: bv := - a
 * - add2:    bv := a1 + a2
 * - sub2:    bv := a1 - a2
 * - mul2:    bv := a1 * a2
 */
extern void bvconst_negate(uint32_t *bv, uint32_t k);
extern void bvconst_add_one(uint32_t *bv, uint32_t k);
extern void bvconst_sub_one(uint32_t *bv, uint32_t k);
extern void bvconst_add(uint32_t *bv, uint32_t k, uint32_t *a);
extern void bvconst_sub(uint32_t *bv, uint32_t k, uint32_t *a);
extern void bvconst_mul(uint32_t *bv, uint32_t k, uint32_t *a);
extern void bvconst_addmul(uint32_t *bv, uint32_t k, uint32_t *a1, uint32_t *a2);
extern void bvconst_submul(uint32_t *bv, uint32_t k, uint32_t *a1, uint32_t *a2);

extern void bvconst_negate2(uint32_t *bv, uint32_t k, uint32_t *a);
extern void bvconst_add2(uint32_t *bv, uint32_t k, uint32_t *a1, uint32_t *a2);
extern void bvconst_sub2(uint32_t *bv, uint32_t k, uint32_t *a1, uint32_t *a2);
extern void bvconst_mul2(uint32_t *bv, uint32_t k, uint32_t *a1, uint32_t *a2);


/*
 * Multiplication by a power
 * - compute bv * (a ^ d) and store the result in bv
 * - bv and a must be distinct and have word size = k
 */
extern void bvconst_mulpower(uint32_t *bv, uint32_t k, uint32_t *a, uint32_t d);


/*
 * DIVISIONS
 */

/*
 * All operations compute the quotient or remainder of a1 divided by a2.
 *
 * The result is stored in bv
 * - a2 must be non-zero
 * - a1, a2, and bv are n-bit constants
 *
 * bvconst_udiv2: quotient, a1 and a2 interpreted as unsigned integers
 * bvconst_urem2: remainder, a1 and a2 interpreted as unsigned integers
 *
 * bvconst_sdiv2: quotient, a1 and a2 interpreted as signed integers
 *                (truncated division, rounding toward 0)
 * bvconst_srem2: remainder, a1 and a2 interpreted as signed integers
 *                (remainder of truncated division, rounding toward 0)
 * bvconst_smod2: remainder, a1 and a2 interpreted as signed integers
 *                (remainder of floor division, rounding toward minus infinity)
 *
 * These are all the division and remainder functions defined in
 * the SMT-LIB notation. (NOTE: the definition of bvsmod in the SMT-LIB
 * website is incorrect).
 *
 * Properties:
 *   a1 = a2 * (udiv a1 a2)  + (urem a1 a2)
 *   a1 = a2 * (sdiv a1 a2)  + (srem a1 a2)
 *   a1 = a2 * (floor a1/a2) + (smod a1 a2)
 *   (sdiv a1 a2) has the same sign as a1/a2
 *   (srem a1 a2) has the same sign as a1
 *   (smod a1 a2) has the same sign as a2
 */
extern void bvconst_udiv2(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2);
extern void bvconst_urem2(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2);
extern void bvconst_sdiv2(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2);
extern void bvconst_srem2(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2);
extern void bvconst_smod2(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2);



/*
 * Same functions except that a zero divider is allowed, using
 * the following rules:
 *  (udiv a 0) = 0b11...1
 *  (urem a 0) = a
 *  (sdiv a 0) = 0b111..1 if a >= 0
 *  (sdiv a 0) = 0b00..01 if a < 0
 *  (srem a 0) = a
 *  (smod a 0) = a
 */
extern void bvconst_udiv2z(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2);
extern void bvconst_urem2z(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2);
extern void bvconst_sdiv2z(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2);
extern void bvconst_srem2z(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2);
extern void bvconst_smod2z(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2);



/*
 * TESTS: all require the constants to be normalized first.
 */

/*
 * Check whether bv is null, k = word size
 */
extern bool bvconst_is_zero(const uint32_t *bv, uint32_t k);

static inline bool bvconst_is_nonzero(const uint32_t *bv, uint32_t k) {
  return ! bvconst_is_zero(bv, k);
}

/*
 * Check whether bv is one, k = word size
 */
extern bool bvconst_is_one(const uint32_t *bv, uint32_t k);


/*
 * Check whether bv is -1 (i.e., 0b11...1)
 * - n = number of bits in bv
 * - bv must be normalized
 */
extern bool bvconst_is_minus_one(const uint32_t *bv, uint32_t n);


/*
 * Check whether bv is 0b100..0 (smallest negative signed integer)
 * - n = number of bits in bv
 * - bv must be normalized.
 */
extern bool bvconst_is_min_signed(const uint32_t *bv, uint32_t n);


/*
 * Check whether bv is 0b0111..1 (largest positive signed integer)
 * - n = number of bits in bv
 * - bv must be normalized
 */
extern bool bvconst_is_max_signed(const uint32_t *bv, uint32_t n);


/*
 * Check whether bv is a power of 2, k = word size
 * - if so return n>=0 such that bv = 2^n
 * - if not return -1
 */
extern int32_t bvconst_is_power_of_two(const uint32_t *bv, uint32_t k);


/*
 * Check whether a and b are equal, k = word size
 * - a and b must have the same size and be normalized
 */
extern bool bvconst_eq(const uint32_t *a, const uint32_t *b, uint32_t k);


/*
 * Check whether a and b are distinct, k = word size
 * - a and b must have the same size and be normalized
 */
static inline bool bvconst_neq(const uint32_t *a, const uint32_t *b, uint32_t k) {
  return ! bvconst_eq(a, b, k);
}


/*
 * Check whether a <= b (unsigned comparison), n = bit size
 * - a and b must have the same size and be normalized
 */
extern bool bvconst_le(const uint32_t *a, const uint32_t *b, uint32_t n);


/*
 * Check whether a >= b (unsigned comparison). n = bit size
 */
static inline bool bvconst_ge(const uint32_t *a, const uint32_t *b, uint32_t n) {
  return bvconst_le(b, a, n);
}


/*
 * Check whether a < b (unsigned comparison), n = bitsize
 * - a and b must have the same size and be normalized.
 */
static inline bool bvconst_lt(const uint32_t *a, const uint32_t *b, uint32_t n) {
  return ! bvconst_le(b, a, n);
}


/*
 * Check whether a > b (unsigned comparison), n = bitsize.
 * - a and b must have the same size and be normalized.
 */
static inline bool bvconst_gt(const uint32_t *a, const uint32_t *b, uint32_t n) {
  return ! bvconst_le(a, b, n);
}


/*
 * Check whether a <= b (signed comparison), n = bitsize
 * - a and b must have the same size and be normalized
 */
extern bool bvconst_sle(const uint32_t *a, const uint32_t *b, uint32_t n);


/*
 * Check whether a >= b (signed comparison), n = bitsize
 */
static inline bool bvconst_sge(const uint32_t *a, const uint32_t *b, uint32_t n) {
  return bvconst_sle(b, a, n);
}


/*
 * Check whether a < b (signed comparison), n = bitsize
 * - a and b must have the same size and be normalized.
 */
static inline bool bvconst_slt(const uint32_t *a, const uint32_t *b, uint32_t n) {
  return ! bvconst_sle(b, a, n);
}


/*
 * Check whether a > b (signed comparison), n = bitsize.
 * - a and b must have the same size and be normalized.
 */
static inline bool bvconst_sgt(const uint32_t *a, const uint32_t *b, uint32_t n) {
  return ! bvconst_sle(a, b, n);
}



/*
 * VARIANTS: using bvconstant structures
 */
static inline void bvconstant_normalize(bvconstant_t *a) {
  bvconst_normalize(a->data, a->bitsize);
}

static inline bool bvconstant_is_normalized(bvconstant_t *a) {
  return bvconst_is_normalized(a->data, a->bitsize);
}

static inline bool bvconstant_is_zero(bvconstant_t *a) {
  assert(bvconstant_is_normalized(a));
  return bvconst_is_zero(a->data, a->width);
}

static inline bool bvconstant_is_nonzero(bvconstant_t *a) {
  return !bvconstant_is_zero(a);
}

static inline bool bvconstant_is_one(bvconstant_t *a) {
  assert(bvconstant_is_normalized(a));
  return bvconst_is_one(a->data, a->width);
}

static inline bool bvconstant_is_minus_one(bvconstant_t *a) {
  assert(bvconstant_is_normalized(a));
  return bvconst_is_minus_one(a->data, a->bitsize);
}

static inline bool bvconstant_is_min_signed(bvconstant_t *a) {
  assert(bvconstant_is_normalized(a));
  return bvconst_is_min_signed(a->data, a->bitsize);
}

static inline bool bvconstant_is_max_signed(bvconstant_t *a) {
  assert(bvconstant_is_normalized(a));
  return bvconst_is_max_signed(a->data, a->bitsize);
}

static inline int32_t bvconstant_is_power_of_two(bvconstant_t *a) {
  return bvconst_is_power_of_two(a->data, a->width);
}

static inline void bvconstant_sub_one(bvconstant_t *a) {
  bvconst_sub_one(a->data, a->width);
}

static inline void bvconstant_add_one(bvconstant_t *a) {
  bvconst_add_one(a->data, a->width);
}

static inline void bvconstant_negate(bvconstant_t *a) {
  bvconst_negate(a->data, a->width);
}


#endif /* __BV_CONSTANTS_H */
