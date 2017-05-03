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
 * TEST OF LOWER/UPPER BOUNDS ON BITVECTORS
 */

#include <assert.h>
#include <inttypes.h>
#include <stdio.h>

#include "api/yices_globals.h"
#include "terms/bv64_constants.h"
#include "terms/term_utils.h"

#include "yices.h"

/*
 * Convert bitconstant to 2s complement
 * - c = constant padded with 0s
 * - n = number of bits
 */
static int64_t signed_bv64(uint64_t c, uint32_t n) {
  int64_t x;

  x = c;
  if (is_neg64(c, n) && n<64) {
    x -= ((int64_t) 1) << n;
  }

  return x;
}

static void test_bounds(term_t t) {
  bvconstant_t aux;
  uint32_t n;
  uint64_t c;

  printf("Testing term t%"PRId32"\n", t);
  yices_pp_term(stdout, t, 100, 10, 0);
  printf("\n");

  n = yices_term_bitsize(t);
  assert(n > 0);
  printf("Number of bits: %"PRIu32"\n\n", n);

  init_bvconstant(&aux);
  bvconstant_set_bitsize(&aux, n);

  upper_bound_unsigned(__yices_globals.terms, t, &aux);
  printf("upper bound, unsigned:   ");
  bvconst_print(stdout, aux.data, n);
  printf("\n");

  lower_bound_unsigned(__yices_globals.terms, t, &aux);
  printf("lower bound, unsigned:   ");
  bvconst_print(stdout, aux.data, n);
  printf("\n");

  upper_bound_signed(__yices_globals.terms, t, &aux);
  printf("upper bound, signed:     ");
  bvconst_print(stdout, aux.data, n);
  printf("\n");

  lower_bound_signed(__yices_globals.terms, t, &aux);
  printf("lower bound, signed:     ");
  bvconst_print(stdout, aux.data, n);
  printf("\n");

  delete_bvconstant(&aux);

  if (n <= 64) {
    c = upper_bound_unsigned64(__yices_globals.terms, t);
    printf("\nupper bound64, unsigned: ");
    bvconst64_print(stdout, c, n);
    printf(" (%"PRIu64")\n", c);

    c = lower_bound_unsigned64(__yices_globals.terms, t);
    printf("lower bound64, unsigned: ");
    bvconst64_print(stdout, c, n);
    printf(" (%"PRIu64")\n", c);

    c = upper_bound_signed64(__yices_globals.terms, t);
    printf("upper bound64, signed:   ");
    bvconst64_print(stdout, c, n);
    printf(" (%"PRId64")\n", signed_bv64(c, n));

    c = lower_bound_signed64(__yices_globals.terms, t);
    printf("lower bound64, signed:   ");
    bvconst64_print(stdout, c, n);
    printf(" (%"PRId64")\n", signed_bv64(c, n));
  }

  printf("----\n\n");
}

static void all_tests(void) {
  uint32_t n;
  type_t bv;
  term_t t;

  for (n=1; n<100; n += 11) {
    bv = yices_bv_type(n);
    t = yices_new_uninterpreted_term(bv);
    yices_set_term_name(t, "u");
    test_bounds(t);
    test_bounds(yices_zero_extend(t, 4));
    test_bounds(yices_sign_extend(t, 4));
    
    test_bounds(yices_bvconst_zero(n));
    test_bounds(yices_bvconst_one(n));
    test_bounds(yices_bvconst_minus_one(n));
  }
}


int main(void) {
  yices_init();
  all_tests();
  yices_exit();

  return 0;
}
