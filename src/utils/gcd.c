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
 * GCD OF UNSIGNED INTEGERS
 */

#include <assert.h>
#include "utils/gcd.h"


/*
 * gcd of two 32bit unsigned positive numbers.
 */
uint32_t gcd32(uint32_t a, uint32_t b) {
  uint32_t x;
  uint32_t k;

  assert(a>0 && b>0);

  k = 1;
  x = a | b;
  while ((x & 1) == 0) {
    k <<= 1;
    x >>= 1;
    a >>= 1;
    b >>= 1;
  }

  do {
    if ((a & 1) == 0) {
      a >>= 1;
    } else if ((b & 1) == 0) {
      b >>= 1;
    } else if (a >= b) {
      a = (a - b) >> 1;
    } else {
      b = (b - a) >> 1;
    }
  } while (a > 0);

  return b * k;
}

/*
 * gcd of two 64bit unsigned positive numbers
 */
uint64_t gcd64(uint64_t a, uint64_t b) {
  uint64_t x;
  uint64_t k;

  assert(a>0 && b>0);

  k = 1;
  x = a | b;
  while ((x & 1) == 0) {
    k <<= 1;
    x >>= 1;
    a >>= 1;
    b >>= 1;
  }

  do {
    if ((a & 1) == 0) {
      a >>= 1;
    } else if ((b & 1) == 0) {
      b >>= 1;
    } else if (a >= b) {
      a = (a - b) >> 1;
    } else {
      b = (b - a) >> 1;
    }
  } while (a > 0);

  return b * k;
}



