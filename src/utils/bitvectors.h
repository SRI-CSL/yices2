/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BIT VECTORS
 */

#ifndef __BIT_VECTORS_H
#define __BIT_VECTORS_H 1

#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include <assert.h>

#include "utils/memalloc.h"


typedef unsigned char byte_t;


/*
 * Allocation of a bit vector of n bits (indexed from 0 to n-1)
 * - not initialized
 */
static inline byte_t *allocate_bitvector(uint32_t n) {
  n = (n + 7) >> 3;
  return safe_malloc(n);
}

/*
 * Extend to n bits. New bits are uninitialized
 */
static inline byte_t *extend_bitvector(byte_t *bv, uint32_t n) {
  n = (n + 7) >> 3;
  return safe_realloc(bv, n);
}



/*
 * Allocate a bitvector of n bits and initialize all to 0
 */
static inline byte_t *allocate_bitvector0(uint32_t n) {
  byte_t *tmp;

  n = (n + 7) >> 3;
  tmp = (byte_t *) safe_malloc(n);
  memset(tmp, 0, n);
  return tmp;
}


/*
 * Extend to n bits. Initialize all new bits to 0
 * - n = new size
 * - m = current size
 * (for this to work, bv must be allocated via allocate_bitvector0)
 */
static inline byte_t *extend_bitvector0(byte_t *bv, uint32_t n, uint32_t m) {
  byte_t *tmp;

  n = (n + 7) >> 3;
  m = (m + 7) >> 3;
  assert(m <= n);
  tmp = (byte_t *) safe_realloc(bv, n);
  memset(tmp + m, 0, n - m);
  return tmp;
}



/*
 * Delete
 */
static inline void delete_bitvector(byte_t *bv) {
  safe_free(bv);
}


/*
 * Clear all the bits:
 * - n must be the full size of bv (as used when bv was allocated)
 */
static inline void clear_bitvector(byte_t *bv, uint32_t n) {
  n = (n + 7) >> 3;
  memset(bv, 0, n);
}


/*
 * Set all the bits
 * - n must be the full size of bv (as used when bv was allocated)
 */
static inline void set_bitvector(byte_t *bv, uint32_t n) {
  n = (n + 7) >> 3;
  memset(bv, 0xff, n);
}


/*
 * Set bit i
 */
static inline void set_bit(byte_t *bv, uint32_t i) {
  uint32_t j;
  byte_t mask;

  j = i >> 3;
  mask = 1 << (i & 0x7);
  bv[j] |= mask;
}

/*
 * Clear bit i
 */
static inline void clr_bit(byte_t *bv, uint32_t i) {
  uint32_t j;
  byte_t mask;

  j = i >> 3;
  mask = 1 << (i & 0x7);
  bv[j] &= ~mask;
}


/*
 * Assign bit i: to 1 if bit is true, to 0 otherwise
 */
static inline void assign_bit_old(byte_t *bv, uint32_t i, bool bit) {
  uint32_t j;
  byte_t mask;

  j = i >> 3;
  mask = 1 << (i & 0x7);
  if (bit) {
    bv[j] |= mask;
  } else {
    bv[j] &= ~mask;
  }
}

// variant: without if-then-else
static inline void assign_bit(byte_t *bv, uint32_t i, bool bit) {
  uint32_t j;
  byte_t x, mask;

  j = (i >> 3);
  mask = 1 << (i & 0x7);
  x = ((byte_t) bit) << (i & 0x7);
  bv[j] ^= (bv[j] ^ x) & mask;
}


/*
 * Flip bit i
 */
static inline void flip_bit(byte_t *bv, uint32_t i) {
  uint32_t j;
  byte_t mask;

  j = i >> 3;
  mask = 1 << (i & 0x7);
  bv[j] ^= mask;
}

/*
 * Test bit i: return 0 if bit i is 0, 1 otherwise
 */
static inline bool tst_bit(byte_t *bv, uint32_t i) {
  uint32_t j;
  byte_t mask;

  j = i >> 3;
  mask = 1 << (i & 0x7);
  return bv[j] & mask; // converted to bool
}


#endif /* __BIT_VECTORS_H */
