/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * Issue #685: the term printer wrote the bits of (bool-to-bv ...) low-order bit
 * first, but the parser reads the first argument as the high-order bit.
 * A printed term must parse back to the same term.
 */
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <yices.h>

static int check(term_t t, const char *expected) {
  char *s = yices_term_to_string(t, 120, 1, 0);
  term_t u;
  int ok = 1;

  if (s == NULL) return 0;
  if (expected != NULL && strcmp(s, expected) != 0) {
    printf("expected %s, got %s\n", expected, s);
    ok = 0;
  }
  u = yices_parse_term(s);
  if (u != t) {
    printf("%s does not parse back to the same term\n", s);
    ok = 0;
  }
  yices_free_string(s);
  return ok;
}

int main(void) {
  term_t p, q, r, bits[4];
  uint32_t i, mask;
  int ok = 1;

  yices_init();
  p = yices_new_uninterpreted_term(yices_bool_type());
  q = yices_new_uninterpreted_term(yices_bool_type());
  r = yices_new_uninterpreted_term(yices_bool_type());
  yices_set_term_name(p, "p");
  yices_set_term_name(q, "q");
  yices_set_term_name(r, "r");

  // arg[0] is the low-order bit
  bits[0] = p; bits[1] = yices_false(); bits[2] = yices_false(); bits[3] = yices_false();
  ok &= check(yices_bvarray(4, bits), "(bool-to-bv false false false p)");

  bits[0] = p; bits[1] = q; bits[2] = r; bits[3] = yices_not(p);
  ok &= check(yices_bvarray(4, bits), "(bool-to-bv (not p) r q p)");

  // round trip for several mixes of constants and variables
  for (mask = 0; mask < 16; mask ++) {
    for (i = 0; i < 4; i ++) {
      bits[i] = ((mask >> i) & 1) ? ((i & 1) ? q : p) : ((i & 2) ? yices_true() : r);
    }
    ok &= check(yices_bvarray(4, bits), NULL);
  }

  yices_exit();
  if (!ok) return 1;
  printf("ok\n");
  return 0;
}
