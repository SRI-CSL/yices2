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

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#ifdef MINGW

static inline long int random(void) {
  return rand();
}

#endif


#define N 10000

static uint32_t random_u32(void) {
  uint32_t a, b;

  a = random();
  b = random();
  return ((a << 4) & (uint32_t) 0xFFFF0000) | (b & (uint32_t) 0xFFFF);
}

int main(void) {
  FILE *f;
  int i;

  f = fopen("seeds", "w");
  if (f == NULL) {
    perror("seeds");
    exit(1);
  }

  for (i=0; i<N; i++) {
    fprintf(f, "%08x\n", random_u32());
  }
  fclose(f);
  return 0;
}
