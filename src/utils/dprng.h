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
 * PRNG using a linear congruence + floating point implementation
 */

#ifndef __DPRNG_H

#include <assert.h>
#include <stdint.h>

#define DPRNG_DEFAULT_SEED 91648253

// Returns a random double 0 <= x < 1. Seed must not be 0.
static inline double drand(double *seed) {
  double x;
  int q;

  x = (*seed) * 1389796;
  q = (int)(x / 2147483647);
  x -= (double)q * 2147483647;
  *seed = x;
  return x / 2147483647;
}

// Returns a random integer 0 <= x < size. Seed must not be 0.
static inline uint32_t irand(double *seed, uint32_t size) {
  uint32_t x = (uint32_t)(drand(seed) * size);
  assert(0 <= x && x < size);
  return x;
}

#endif
