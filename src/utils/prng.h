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
 * Simple PRNG based on a linear congruence modulo 2^32.
 *
 * Recurrence X_{t+1} = (a X_t + b) mod 2^32
 * - X_0 is the seed,
 * - a = 1664525,
 * - b = 1013904223
 * (Source: Wikipedia + Knuth's Art of Computer Programming, Vol. 2)
 *
 * The low-order bits are not random.
 *
 * Note: the state of the PRNG (variable seed) is local.
 * So every file that imports this will have its own copy of the PRNG,
 * and all copies have the same default seed.
 */

#ifndef __PRNG_H
#define __PRNG_H

#include <stdint.h>

#define PRNG_MULTIPLIER 1664525
#define PRNG_CONSTANT   1013904223

#define PRNG_DEFAULT_SEED 0xabcdef98

static inline void random_seed(uint32_t *seedp, uint32_t s) {
  *seedp = s;
}

static inline uint32_t random_uint32(uint32_t *seedp) {
  uint32_t x = *seedp;
  *seedp = x * ((uint32_t) PRNG_MULTIPLIER) + ((uint32_t) PRNG_CONSTANT);
  return x;
}

static inline int32_t random_int32(uint32_t *seedp) {
  return (int32_t) random_uint32(seedp);
}

// random integer between 0 and n-1 (remove 8 low-order bits)
static inline uint32_t random_uint(uint32_t *seedp, uint32_t n) {
  return (random_uint32(seedp) >> 8) % n;
}


#endif


