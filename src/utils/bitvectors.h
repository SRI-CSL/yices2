/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
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
 * Wrapper around memset to avoid warnings with sanitize
 * - malloc(0) is allowed to return NULL
 * - the C standard does not say whether memset(NULL, c, 0) is allowed
 * - compiling with the address sanitizer complains on memset(NUL,...)
 * - so we check for that here.
 */
static inline void do_memset(byte_t *b, int c, uint32_t n) {
  if (n > 0) memset(b, c, n);
}

/*
 * Allocate a bitvector of n bits and initialize all to 0
 */
static inline byte_t *allocate_bitvector0(uint32_t n) {
  byte_t *tmp;

  n = (n + 7) >> 3;
  tmp = (byte_t *) safe_malloc(n);
  do_memset(tmp, 0, n);
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
  do_memset(tmp + m, 0, n - m);
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
  do_memset(bv, 0, n);
}


/*
 * Set all the bits
 * - n must be the full size of bv (as used when bv was allocated)
 */
static inline void set_bitvector(byte_t *bv, uint32_t n) {
  n = (n + 7) >> 3;
  do_memset(bv, 0xff, n);
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
