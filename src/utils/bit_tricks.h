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
 * Low-level bit and bit-mask operations
 * -------------------------------------
 *
 * uint32_t ctz(uint32_t x): number of trailing zeros
 * - return the index (between 0 and 31) of the lowest-order bit
 *   of x that's not 0
 * - x must be nonzero
 *
 * uint32_t clz(uint32_t x): number of leading zeros in x
 * - x must be nonzero
 *
 * uint32_t ctz64(uint64_t x):
 * - return the index (between 0 and 63) of the lowest-order bit
 *   of x that's not 0
 * - x must be nonzero
 *
 * uint32_t clz64(uint64_t x):
 * - number of leading zeros in x
 * - x must be nonzero
 *
 * uint32_t binlog(uint32_t x): return the smallest k such that
 * - x <= 2^k
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

#ifdef NETBSD
/* NetBSD has popcount in libc. */
#include <strings.h>
#endif


#ifdef __GNUC__

/*
 * GCC defines
 * __builtin_ctz(unsigned int)
 * __builtin_ctzl(unsigned long)
 * __builtin_ctzll(unsigned long long)
 *
 * __builtin_clz(unsigned int)
 * __builtin_clzl(unsigned long)
 * __builtin_clzll(unsigned long long)
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


/*
 * 32bit operations
 */
#if (UINT_MAX < UINT32_MAX)
//#warning "bit_tricks: uint32_t is (unsigned long)"

static inline uint32_t ctz(uint32_t x) {
  assert(x != 0);
  return __builtin_ctzl(x);
}

static inline uint32_t clz(uint32_t x) {
  assert(x != 0);
  return __builtin_clzl(x);
}

#ifndef NETBSD
static inline uint32_t popcount32(uint32_t x) {
  return __builtin_popcountl(x);
}
#endif

#else
//#warning "ctz: uint32_t is (unsigned int)"

static inline uint32_t ctz(uint32_t x) {
  assert(x != 0);
  return __builtin_ctz(x);
}

static inline uint32_t clz(uint32_t x) {
  assert(x != 0);
  return __builtin_clz(x);
}

#ifndef NETBSD
static inline uint32_t popcount32(uint32_t x) {
  return __builtin_popcount(x);
}
#endif

#endif


/*
 * 64bit operations
 */
#if (ULONG_MAX < UINT64_MAX)
// #warning "bit_tricks: uint64_t is (unsigned long long)

static inline uint32_t ctz64(uint64_t x) {
  assert(x != 0);
  return __builtin_ctzll(x);
}

static inline uint32_t clz64(uint64_t x) {
  assert(x != 0);
  return __builtin_clzll(x);
}

#ifndef NETBSD
static inline uint32_t popcount64(uint64_t x) {
  return __builtin_popcountll(x);
}
#endif

#else
// #warning "bit_tricks: uint64_t is (unsigned long)

static inline uint32_t ctz64(uint64_t x) {
  assert(x != 0);
  return __builtin_ctzl(x);
}

static inline uint32_t clz64(uint64_t x) {
  assert(x != 0);
  return __builtin_clzl(x);
}

#ifndef NETBSD
static inline uint32_t popcount64(uint64_t x) {
  return __builtin_popcountl(x);
}
#endif

#endif // 64bit versions


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

static inline uint32_t clz(uint32_t x) {
  uint32_t m, i;

  assert(x != 0);
  m = 0x80000000u;
  i = 0;
  while ((x & m) == 0) {
    i ++;
    m >>= 1;
  }
  return i;
}

static inline uint32_t clz64(uint64_t x) {
  uint64_t m, i;

  assert(x != 0);
  m = 0x8000000000000000u;
  i = 0;
  while ((x & m) == 0) {
    i ++;
    m >>= 1;
  }
  return i;
}

#ifndef NETBSD
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
#endif /* #ifndef NETBSD */

#endif


static inline uint32_t binlog(uint32_t x) {
  uint32_t k;

  k = (x == 0) ? 31 : clz(x);
  assert(k < 32);
  return (x & (~0x80000000u >> k)) ? 32 - k : 31 - k;
}



#endif /* __BIT_TRICKS_H */
