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

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>

int main(void) {
  uint32_t n;
  uint64_t aux, mask, neg;

  for (n=1; n<=64; n++) {
    aux = ((uint64_t) 1) << n;
    mask = ~((uint64_t) 0) >> (64 - n);
    neg = - mask;
    printf("n = %2"PRIu32", aux = %016"PRIx64" mask = %016"PRIx64", neg = %016"PRIx64"\n", n, aux, mask, neg);
  }

  return 0;
}
