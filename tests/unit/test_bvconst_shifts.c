/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test the shift operations in bv_constants and bv64_constants
 */

#include <stdio.h>
#include <inttypes.h>

#include "terms/bv64_constants.h"
#include "terms/bv_constants.h"

/*
 * Test shift a by b: both stored as 64bit integers
 * - n = number of bits in a and b
 */
static void test_shift64(uint64_t a, uint64_t b, uint32_t n) {
  uint64_t lshl, lshr, ashr;

  a = norm64(a, n);
  b = norm64(b, n);

  lshl = bvconst64_lshl(a, b, n);
  assert(lshl == norm64(lshl, n));

  lshr = bvconst64_lshr(a, b, n);
  assert(lshr == norm64(lshr, n));

  ashr = bvconst64_ashr(a, b, n);
  assert(ashr == norm64(ashr, n));

  printf(" a = ");
  bvconst64_print(stdout, a, n);
  printf("\n");
  printf(" b = ");
  bvconst64_print(stdout, b, n);
  printf("\n");
  printf(" lshl(a, b) = ");
  bvconst64_print(stdout, lshl, n);
  printf("\n");
  printf(" lshr(a, b) = ");
  bvconst64_print(stdout, lshr, n);
  printf("\n");
  printf(" ashr(a, b) = ");
  bvconst64_print(stdout, ashr, n);
  printf("\n\n");
}

/*
 * Same thing for x and y stored as arrays of words
 */
static void test_shift(uint32_t *x, uint32_t *y, uint32_t n) {
  uint32_t lshl[2];
  uint32_t lshr[2];
  uint32_t ashr[2];

  assert(0 < n && n <= 64);

  bvconst_normalize(x, n);
  bvconst_normalize(y, n);

  bvconst_lshl(lshl, x, y, n);
  bvconst_lshr(lshr, x, y, n);
  bvconst_ashr(ashr, x, y, n);

  printf(" a = ");
  bvconst_print(stdout, x, n);
  printf("\n");
  printf(" b = ");
  bvconst_print(stdout, y, n);
  printf("\n");
  printf(" lshl(a, b) = ");
  bvconst_print(stdout, lshl, n);
  printf("\n");
  printf(" lshr(a, b) = ");
  bvconst_print(stdout, lshr, n);
  printf("\n");
  printf(" ashr(a, b) = ");
  bvconst_print(stdout, ashr, n);
  printf("\n\n");
}


int main(void) {
  uint32_t i, j;
  uint64_t a, b;
  uint32_t x[2], y[2];

  printf("--- bit size = 5 ---\n");
  for (i=0; i<32; i++) {
    for (j=0; j<7; j++) {
      a = i;
      b = j;
      test_shift64(a, b, 5);
      x[0] = i; x[1] = 0;
      y[0] = j; y[1] = 0;
      test_shift(x, y, 5);
      printf("---\n");
    }
  }

  // more tests with size = 64bits
  a = 6;
  test_shift64(a << 4, 0, 64);
  test_shift64(a << 4, 1, 64);
  test_shift64(a << 4, 2, 64);
  test_shift64(a << 4, 3, 64);
  test_shift64(a << 4, 4, 64);
  test_shift64(a << 4, 5, 64);
  test_shift64(a << 4, 63, 64);
  test_shift64(a << 4, 64, 64);
  test_shift64(a << 4, 65, 64);

  a ^= ~((uint64_t) 0);
  test_shift64(a << 4, 0, 64);
  test_shift64(a << 4, 1, 64);
  test_shift64(a << 4, 2, 64);
  test_shift64(a << 4, 3, 64);
  test_shift64(a << 4, 4, 64);
  test_shift64(a << 4, 5, 64);
  test_shift64(a << 4, 63, 64);
  test_shift64(a << 4, 64, 64);
  test_shift64(a << 4, 65, 64);


  x[0] = 6 << 4;
  x[1] = 0;
  y[0] = 0;
  y[1] = 0;
  test_shift(x, y, 62);
  y[0] = 1;
  test_shift(x, y, 62);
  y[0] = 10;
  test_shift(x, y, 62);
  y[1] = 2;
  test_shift(x, y, 62);

  x[1] = 0xFF000000;
  x[0] = 0x55555555;
  y[0] = 0;
  y[1] = 0;
  test_shift(x, y, 64);
  y[0] = 1;
  test_shift(x, y, 64);
  y[0] = 10;
  test_shift(x, y, 64);
  y[1] = 2;
  test_shift(x, y, 64);

  return 0;
}
