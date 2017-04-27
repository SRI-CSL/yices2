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
#include <inttypes.h>

#include "utils/int_powers.h"

int main(void) {
  uint32_t d;

  // powers of 0
  for (d=0; d<16; d++) {
    printf("pow32(0, %"PRIu32") = %"PRIu32"\n", d, upower32(0, d));
    printf("pow64(0, %"PRIu32") = %"PRIu64"\n", d, upower64(0, d));
  }

  // powers of 1
  for (d=0; d<16; d++) {
    printf("pow32(1, %"PRIu32") = %"PRIu32"\n", d, upower32(1, d));
    printf("pow64(1, %"PRIu32") = %"PRIu64"\n", d, upower64(1, d));
  }

  // powers of 2
  for (d=0; d<80; d++) {
    printf("pow32(2, %"PRIu32") = %"PRIu32"\n", d, upower32(2, d));
    printf("pow64(2, %"PRIu32") = %"PRIu64"\n", d, upower64(2, d));
  }

  return 0;
}
