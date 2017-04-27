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
#include <string.h>
#include <inttypes.h>


#ifdef MINGW
/*
 * Need some version of random() and srandom()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

static inline void srandom(unsigned int seed) {
  srand(seed);
}

#endif


static char *kw[] = {
  "*",
  "+",
  "-",
  "/",
  ":assumption",
  ":extrafuns",
  ":extrapreds",
  ":extrasorts",
  ":formula",
  ":logic",
  ":nopat",
  ":notes",
  ":pat",
  ":status",
  "<",
  "<=",
  "=",
  ">",
  ">=",
  "Array",
  "Array1",
  "Array2",
  "BitVec",
  "Int",
  "Real",
  "U",
  "and",
  "benchmark",
  "bit0",
  "bit1",
  "bvadd",
  "bvand",
  "bvashr",
  "bvcomp",
  "bvgeq",
  "bvgt",
  "bvleq",
  "bvlshr",
  "bvlt",
  "bvmul",
  "bvnand",
  "bvneg",
  "bvnor",
  "bvnot",
  "bvor",
  "bvredand",
  "bvredor",
  "bvsdiv",
  "bvsge",
  "bvsgeq",
  "bvsgt",
  "bvshl",
  "bvsle",
  "bvsleq",
  "bvslt",
  "bvsmod",
  "bvsrem",
  "bvsub",
  "bvudiv",
  "bvuge",
  "bvugt",
  "bvule",
  "bvult",
  "bvurem",
  "bvxnor",
  "bvxor",
  "concat",
  "distinct",
  "exists",
  "extract",
  "false",
  "flet",
  "forall",
  "if_then_else",
  "iff",
  "implies",
  "ite",
  "let",
  "not",
  "or",
  "repeat",
  "rotate_left",
  "rotate_right",
  "sat",
  "select",
  "shift_left0",
  "shift_left1",
  "shift_right0",
  "shift_right1",
  "sign_extend",
  "store",
  "true",
  "unknown",
  "unsat",
  "xor",
  "zero_extend",
  "~",
};

#define NKEYWORDS 97

uint32_t hash[NKEYWORDS];
uint8_t test[256];
uint8_t key[256];

uint32_t hash_string(char *s) {
  uint32_t h, x;

  h = 5;
  x = *s;
  while (x != 0) {
    h += key[x];
    s ++;
    x = *s;
  }

  return h;
}

int main(void) {
  int32_t i;
  uint32_t h, n;
  char *s;

  srandom(49238);
  for (i=0; i<256; i++) {
    key[i] = random() & 0xff;
  }
  for (i=0; i<NKEYWORDS; i++) {
    s = kw[i];
    printf("%s:", kw[i]);
    while (*s != '\0') {
      printf(" %d", *s);
      s++;
    }
    printf("\n");
  }
  printf("\n");
  for (i=0; i<NKEYWORDS; i++) {
    h = hash_string(kw[i]);
    hash[i] = h;
    printf("%20s    %10"PRIu32" %3"PRIu32" %3"PRIu32" %3"PRIu32"\n", kw[i], h, (h & 0x1ff), (h & 0xff), (h & 0x7f));
  }

  for (i=0; i<256; i++) test[i] = 0;

  n = 0;
  for (i=0; i<NKEYWORDS; i++) {
    h = hash[i] & 0xff;
    if (test[h] > 0) n ++;
    test[h] ++;
  }

  printf("\n%"PRIu32" collisions:\n", n);
  for (h=0; h<256; h++) {
    if (test[h] > 1) {
      printf("%3"PRIu32" ", h);
    }
  }
  printf("\n");

  return 0;
}
