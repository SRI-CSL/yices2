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

#include "utils/int_powers.h"

uint32_t upower32(uint32_t x, uint32_t d) {
  uint32_t y;

  y = 1;
  while (d != 0) {
    if ((d & 1) != 0) {
      y *= x;
    }
    d >>= 1;
    x *= x;
  }
  return y;
}


uint64_t upower64(uint64_t x, uint32_t d) {
  uint64_t y;

  y = 1;
  while (d != 0) {
    if ((d & 1) != 0) {
      y *= x;
    }
    d >>= 1;
    x *= x;
  }
  return y;
}
