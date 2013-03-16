/*
 * Low-level bit and bit-mask operations
 * -------------------------------------
 *
 * uint32_t ctz(uint32_t x):
 * - return the index (between 0 and 31) of the lowest-order bit 
 *   of x that's not 0
 * - x must be nonzero
 *
 * uint32_t ctz64(uint64_t x):
 * - return the index (between 0 and 63) of the lowest-order bit
 *   of x that's not 0
 * - x must be nonzero
 *
 * uint32_t popcount32(uint32_t x):
 * uint32_t popcount64(uint64_t x):
 * - return the number of 1-bits in x
 *
 * GCC defines these functions. For other compilers we give a 
 * default (naive) implementation.
 *
 */

#ifndef __BIT_TRICKS_H
#define __BIT_TRICKS_H

#include <stdint.h>
#include <assert.h>


#ifdef __GNUC__

/*
 * GCC defines
 * __builtin_ctz(unsigned int)
 * __builtin_ctzl(unsigned long)
 * __builtin_ctzll(unsigned long long)
 *
 * __builtin_popcount(unsigned int)
 * __builtin_popcountl(unsigned long)
 * __builtin_popcountll(unsigned long long)
 *
 * Don't know if they exist on old GCC versions.
 */

#include <limits.h>

/*
 * The C standard requires that 
 *     (unsigned int) is at least 16bits
 *     (unsigned long) is at least 32bits
 * and (unsigned long long) is at least 64bits
 */

static inline uint32_t ctz(uint32_t x) {
  assert(x != 0);
#if (UINT_MAX < UINT32_MAX)
  //#warning "ctz: uint32_t is not (unsigned int)"
  return __builtin_ctzl(x);
#else
  return __builtin_ctz(x);
#endif
}

static inline uint32_t ctz64(uint64_t x) {
  assert(x != 0);
#if (ULONG_MAX < UINT64_MAX) 
  return __builtin_ctzll(x);
#else 
  return __builtin_ctzl(x);
#endif
}


static inline uint32_t popcount32(uint32_t x) {
#if (UINT_MAX < UINT32_MAX)
  //#warning "popcount32: uint32_t is not (unsigned int)"
  return __builtin_popcountl(x);
#else 
  return __builtin_popcount(x);
#endif
}


static inline uint32_t popcount64(uint64_t x) {
#if (ULONG_MAX < UINT64_MAX)
  //#warning "popcount64: uint64_t is not (unsigned long)"
  return __builtin_popcountll(x);
#else
  return __builtin_popcountl(x);
#endif
}



#else 


/*
 * Not GCC
 */
static inline uint32_t ctz(uint32_t x) {
  uint32_t m, i;

  assert(x != 0);
  m = 1;
  i = 0;
  while ((x & m) == 0) {
    i ++;
    m += m;
  }
  return i;
}

static inline uint32_t ctz64(uint64_t x) {
  uint64_t m;
  uint32_t i;

  assert(x != 0);
  m = 1;
  i = 0;
  while ((x & m) == 0) {
    i ++;
    m += m;
  }
  return i;
}

static inline uint32_t popcount32(uint32_t x) {
  uint32_t c;

  c = 0;
  while (x != 0) {
    x &= (x - 1); // clear least significant bit
    c ++;
  }

  return c;
}

static inline uint32_t popcount64(uint64_t x) {
  uint32_t c;

  c = 0;
  while (x != 0) {
    x &= (x - 1);  // clear least significant bit
    c ++;
  }

  return c;
}

#endif 


#endif /* __BIT_TRICKS_H */
