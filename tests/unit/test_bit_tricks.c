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

#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <inttypes.h>

#include "utils/cputime.h"
#include "utils/bit_tricks.h"


/*
 * Get number of trailing 0-bits in x for non-zero x
 */
static inline uint32_t naive_ctz(uint32_t x) {
  uint32_t m, i;

  assert(x != 0);
  m = 0x1;
  i = 0;
  while ((x & m) == 0) {
    i ++;
    m <<= 1;
  }
  return i;
}



/*
 * Same thing for a 64bit number x
 */
static inline uint32_t naive_ctz64(uint64_t x) {
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


/*
 * Number of leading 0 bits in x
 */
static inline uint32_t naive_clz(uint32_t x) {
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


/*
 * Number of 1 bits in x
 */
static inline uint32_t naive_popcount32(uint32_t x) {
  uint32_t c;

  c = 0;
  while (x != 0) {
    x &= (x - 1); // clear least significant bit
    c ++;
  }

  return c;
}


/*
 * Number of 1 bits in 64 bit integer x
 */
static inline uint32_t naive_popcount64(uint64_t x) {
  uint32_t c;

  c = 0;
  while (x != 0) {
    x &= (x - 1);  // clear least significant bit
    c ++;
  }

  return c;
}


#define N 500000000
#define X (1<<31)

int main(void) {
  uint32_t i, n;
  uint64_t x;
  double c, d;

  printf("=== Base test ===\n");
  for (i=0; i<32; i++) {
    n = 1<<i;
    printf("naive_ctz(%"PRIu32") = %"PRIu32"\n", n, naive_ctz(n));
  }
  printf("\n");

  for (i=0; i<32; i++) {
    n = 1<<i;
    printf("__builtin_ctz(%"PRIu32") = %"PRIu32"\n", n, ctz(n));
  }
  printf("\n");

  for (i=0; i<64; i++) {
    x = ((uint64_t) 1) << i;
    printf("native_ctz64(%"PRIu64") = %"PRIu32"\n", x, naive_ctz64(x));
  }
  printf("\n");

  for (i=0; i<64; i++) {
    x = ((uint64_t) 1) << i;
    printf("__builtin_ctz64(%"PRIu64") = %"PRIu32"\n", x, ctz64(x));
  }
  printf("\n");

  for (i=0; i<32; i++) {
    n = 1<<i;
    printf("naive_clz(%"PRIu32") = %"PRIu32"\n", n, naive_clz(n));
  }
  printf("\n");

  for (i=0; i<32; i++) {
    n = 1<<i;
    printf("__builtin_clz(%"PRIu32") = %"PRIu32"\n", n, clz(n));
  }
  printf("\n");

  printf("binlog(0) = %"PRIu32"\n", binlog(0));
  printf("binlog(1) = %"PRIu32"\n", binlog(1));
  for (i=1; i<32; i++) {
    n = 1<<i;
    printf("binlog(%"PRIu32") = %"PRIu32"\n", n, binlog(n));
    printf("binlog(%"PRIu32") = %"PRIu32"\n", n+1, binlog(n+1));
  }
  printf("\n");

  n = 5;
  for (i=0; i<60; i++) {
    printf("naive_popcount(%"PRIu32") = %"PRIu32"\n", n, naive_popcount32(n));
    printf("builtin_popcount(%"PRIu32") = %"PRIu32"\n", n, popcount32(n));
    n *= 3;
  }
  printf("\n");

  x = 5;
  for (i=0; i<100; i++) {
    printf("naive_popcount(%"PRIu64") = %"PRIu32"\n", x, naive_popcount64(x));
    printf("builtin_popcount(%"PRIu64") = %"PRIu32"\n", x, popcount64(x));
    x *= 7;
  }
  printf("\n");

  for (i=0; i<32; i++) {
    n = 1<<i;
    printf("naive_popcount(%"PRIu32") = %"PRIu32"\n", n, naive_popcount32(n));
    printf("builtin_popcount(%"PRIu32") = %"PRIu32"\n", n, popcount32(n));
    n --;
    printf("naive_popcount(%"PRIu32") = %"PRIu32"\n", n, naive_popcount32(n));
    printf("builtin_popcount(%"PRIu32") = %"PRIu32"\n", n, popcount32(n));
  }
  printf("\n");

  for (i=0; i<64; i++) {
    x = ((uint64_t) 1)<<i;
    printf("naive_popcount(%"PRIu64") = %"PRIu32"\n", x, naive_popcount64(x));
    printf("builtin_popcount(%"PRIu64") = %"PRIu32"\n", x, popcount64(x));
    x --;
    printf("naive_popcount(%"PRIu64") = %"PRIu32"\n", x, naive_popcount64(x));
    printf("builtin_popcount(%"PRIu64") = %"PRIu32"\n", x, popcount64(x));
  }
  printf("\n");
  fflush(stdout);

  i = 0;
  c = get_cpu_time();
  for (n=0; n<N; n++) {
    i = naive_ctz(n|X);
    i += naive_ctz((n<<8) | X);
    i += naive_ctz((n<<16)| X);
    i += naive_ctz((n<<24)| X);
  }
  d = get_cpu_time();
  printf("Naive ctz:    %.2f s (i = %"PRIu32")\n", (d - c), i);


  i = 0;
  c = get_cpu_time();
  for (n=0; n<N; n++) {
    i = ctz(n|X);
    i += ctz((n<<8)|X);
    i += ctz((n<<16)|X);
    i += ctz((n<<24)|X);
  }
  d = get_cpu_time();
  printf("Built-in ctz: %.2f s (i = %"PRIu32")\n\n", (d - c), i);


  return 0;
}
