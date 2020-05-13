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
 * Test the division and remainder operations
 * on bitvector constants.
 */

#include <stdio.h>
#include <inttypes.h>

#include <gmp.h>

#include "terms/bv64_constants.h"
#include "terms/bv_constants.h"


/*
 * Test x divided by y
 * - both stored as uin64_t, interpreted as n-bit constants
 */
static void test_bv64(uint64_t x, uint64_t y, uint32_t n) {
  uint64_t udiv, urem, sdiv, srem, smod;

  x = norm64(x, n);
  y = norm64(y, n);
  udiv = bvconst64_udiv2z(x, y, n);
  urem = bvconst64_urem2z(x, y, n);
  sdiv = bvconst64_sdiv2z(x, y, n);
  srem = bvconst64_srem2z(x, y, n);
  smod = bvconst64_smod2z(x, y, n);

  printf("udiv(%"PRIu64", %"PRIu64") = %"PRIu64", ", x, y, udiv);
  printf("urem(%"PRIu64", %"PRIu64") = %"PRIu64", ", x, y, urem);
  printf("sdiv(%"PRIu64", %"PRIu64") = %"PRIu64", ", x, y, sdiv);
  printf("srem(%"PRIu64", %"PRIu64") = %"PRIu64", ", x, y, srem);
  printf("smod(%"PRIu64", %"PRIu64") = %"PRIu64"\n", x, y, smod);
}



static inline uint32_t bv32(uint32_t *x) {
  return bvconst_get32(x);
}

static inline uint64_t bv64(uint32_t *x) {
  return bvconst_get64(x);
}

/*
 * Test x divided by y
 * - both stored as word vectors, interpreted as n-bit constants
 * - n must be no more than 64;
 */
static void test_bv(uint32_t *x, uint32_t *y, uint32_t n) {
  uint32_t udiv[2], urem[2];
  uint32_t sdiv[2], srem[2], smod[2];

  assert(0 < n && n <= 64);

  bvconst_normalize(x, n);
  bvconst_normalize(y, n);

  bvconst_udiv2z(udiv, n, x, y);
  bvconst_normalize(udiv, n);
  bvconst_urem2z(urem, n, x, y);
  bvconst_normalize(urem, n);
  bvconst_sdiv2z(sdiv, n, x, y);
  bvconst_normalize(sdiv, n);
  bvconst_srem2z(srem, n, x, y);
  bvconst_normalize(srem, n);
  bvconst_smod2z(smod, n, x, y);
  bvconst_normalize(smod, n);

  if (n <= 32) {
    printf("udiv(%"PRIu32", %"PRIu32") = %"PRIu32", ", bv32(x), bv32(y), bv32(udiv));
    printf("urem(%"PRIu32", %"PRIu32") = %"PRIu32", ", bv32(x), bv32(y), bv32(urem));
    printf("sdiv(%"PRIu32", %"PRIu32") = %"PRIu32", ", bv32(x), bv32(y), bv32(sdiv));
    printf("srem(%"PRIu32", %"PRIu32") = %"PRIu32", ", bv32(x), bv32(y), bv32(srem));
    printf("smod(%"PRIu32", %"PRIu32") = %"PRIu32"\n", bv32(x), bv32(y), bv32(smod));
  } else {
    printf("udiv(%"PRIu64", %"PRIu64") = %"PRIu64", ", bv64(x), bv64(y), bv64(udiv));
    printf("urem(%"PRIu64", %"PRIu64") = %"PRIu64", ", bv64(x), bv64(y), bv64(urem));
    printf("sdiv(%"PRIu64", %"PRIu64") = %"PRIu64", ", bv64(x), bv64(y), bv64(sdiv));
    printf("srem(%"PRIu64", %"PRIu64") = %"PRIu64", ", bv64(x), bv64(y), bv64(srem));
    printf("smod(%"PRIu64", %"PRIu64") = %"PRIu64"\n", bv64(x), bv64(y), bv64(smod));
  }
}



int main(void) {
  uint32_t i, j;
  uint32_t x[2], y[2];
  uint64_t a, b;

  printf("--- bit size = 5 ---\n");
  for (i=0; i<32; i++) {
    for (j=0; j<32; j++) {
      a = i;
      b = j;
      test_bv64(a, b, 5);
      x[0] = i; x[1] = 0;
      y[0] = j; y[1] = 0;
      test_bv(x, y, 5);
      printf("---\n");
    }
  }

  printf("--- overflow tests ---\n");
  for (i=1; i<=64; i++) {
    a = min_signed64(i); // 2^(i-1)
    b = mask64(i);       // 2^i - 1 
    printf("udiv(%"PRIu64", %"PRIu64") = %"PRIu64"\n", a, b, bvconst64_udiv2z(a, b, i));
    printf("urem(%"PRIu64", %"PRIu64") = %"PRIu64"\n", a, b, bvconst64_urem2z(a, b, i));
    printf("sdiv(%"PRIu64", %"PRIu64") = %"PRIu64"\n", a, b, bvconst64_sdiv2z(a, b, i));
    printf("srem(%"PRIu64", %"PRIu64") = %"PRIu64"\n", a, b, bvconst64_srem2z(a, b, i));
    printf("smod(%"PRIu64", %"PRIu64") = %"PRIu64"\n", a, b, bvconst64_smod2z(a, b, i));
    printf("---\n");
  }

  return 0;
}
