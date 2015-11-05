/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
