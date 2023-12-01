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
 * EXPONENTIATION OF INTEGERS
 */

#ifndef __INT_POWERS_H
#define __INT_POWERS_H

#include <stdbool.h>
#include <stdint.h>

/*
 * Return true iff N is a power of two.
 */
static inline bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
				   
/*
 * Return x^d (modulo 2^32 or 2^64)
 */
extern uint32_t upower32(uint32_t x, uint32_t d);
extern uint64_t upower64(uint64_t x, uint32_t d);

#endif /* __INT_POWERS_H */
