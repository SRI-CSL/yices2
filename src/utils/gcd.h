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

#ifndef __GCD_H
#define __GCD_H

#include <stdint.h>

/*
 * gcd of two unsigned integers
 * both a and b must be positive.
 */
extern uint32_t gcd32(uint32_t a, uint32_t b);
extern uint64_t gcd64(uint64_t a, uint64_t b);

#endif /* __GCD_H */
