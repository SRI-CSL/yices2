/*
 * Test the shift operations in bv_constants and bv64_constants
 */

#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>

#include "bv_constants.h"
#include "bv64_constants.h"
#include "threads.h"

/*
 * Test shift a by b: both stored as 64bit integers
 * - n = number of bits in a and b
 */
static void test_shift64(FILE* output, uint64_t a, uint64_t b, uint32_t n) {
  uint64_t lshl, lshr, ashr;

  a = norm64(a, n);
  b = norm64(b, n);

  lshl = bvconst64_lshl(a, b, n);
  assert(lshl == norm64(lshl, n));

  lshr = bvconst64_lshr(a, b, n);
  assert(lshr == norm64(lshr, n));

  ashr = bvconst64_ashr(a, b, n);
  assert(ashr == norm64(ashr, n));

  fprintf(output, " a = ");
  bvconst64_print(output, a, n);
  fprintf(output, "\n");
  fprintf(output, " b = ");
  bvconst64_print(output, b, n);
  fprintf(output, "\n");
  fprintf(output, " lshl(a, b) = ");
  bvconst64_print(output, lshl, n);
  fprintf(output, "\n");
  fprintf(output, " lshr(a, b) = ");
  bvconst64_print(output, lshr, n);
  fprintf(output, "\n");
  fprintf(output, " ashr(a, b) = ");
  bvconst64_print(output, ashr, n);
  fprintf(output, "\n\n");
}

/*
 * Same thing for x and y stored as arrays of words
 */
static void test_shift(FILE* output, uint32_t *x, uint32_t *y, uint32_t n) {
  uint32_t lshl[2];
  uint32_t lshr[2];
  uint32_t ashr[2];

  assert(0 < n && n <= 64);

  bvconst_normalize(x, n);
  bvconst_normalize(y, n);

  bvconst_lshl(lshl, x, y, n);
  bvconst_lshr(lshr, x, y, n);
  bvconst_ashr(ashr, x, y, n);

  fprintf(output, " a = ");
  bvconst_print(output, x, n);
  fprintf(output, "\n");
  fprintf(output, " b = ");
  bvconst_print(output, y, n);
  fprintf(output, "\n");
  fprintf(output, " lshl(a, b) = ");
  bvconst_print(output, lshl, n);
  fprintf(output, "\n");
  fprintf(output, " lshr(a, b) = ");
  bvconst_print(output, lshr, n);
  fprintf(output, "\n");
  fprintf(output, " ashr(a, b) = ");
  bvconst_print(output, ashr, n);
  fprintf(output, "\n\n");
}




yices_thread_result_t YICES_THREAD_ATTR test_thread(void* arg){
  thread_data_t* tdata = (thread_data_t *)arg;
  FILE* output = tdata->output;

  uint32_t i, j;
  uint64_t a, b;
  uint32_t x[2], y[2];

  fprintf(output, "--- bit size = 5 ---\n");
  for (i=0; i<32; i++) {
    for (j=0; j<7; j++) {
      a = i;
      b = j;
      test_shift64(output, a, b, 5);
      x[0] = i; x[1] = 0;
      y[0] = j; y[1] = 0;
      test_shift(output, x, y, 5);
      fprintf(output, "---\n");
    }
  }

  // more tests with size = 64bits
  a = 6;
  test_shift64(output, a << 4, 0, 64);
  test_shift64(output, a << 4, 1, 64);
  test_shift64(output, a << 4, 2, 64);
  test_shift64(output, a << 4, 3, 64);
  test_shift64(output, a << 4, 4, 64);
  test_shift64(output, a << 4, 5, 64);
  test_shift64(output, a << 4, 63, 64);
  test_shift64(output, a << 4, 64, 64);
  test_shift64(output, a << 4, 65, 64);

  a ^= ~((uint64_t) 0);
  test_shift64(output, a << 4, 0, 64);
  test_shift64(output, a << 4, 1, 64);
  test_shift64(output, a << 4, 2, 64);
  test_shift64(output, a << 4, 3, 64);
  test_shift64(output, a << 4, 4, 64);
  test_shift64(output, a << 4, 5, 64);
  test_shift64(output, a << 4, 63, 64);
  test_shift64(output, a << 4, 64, 64);
  test_shift64(output, a << 4, 65, 64);


  x[0] = 6 << 4;
  x[1] = 0;
  y[0] = 0;
  y[1] = 0;
  test_shift(output, x, y, 62);
  y[0] = 1;
  test_shift(output, x, y, 62);
  y[0] = 10;
  test_shift(output, x, y, 62);
  y[1] = 2;
  test_shift(output, x, y, 62);

  x[1] = 0xFF000000;
  x[0] = 0x55555555;
  y[0] = 0;
  y[1] = 0;
  test_shift(output, x, y, 64);
  y[0] = 1;
  test_shift(output, x, y, 64);
  y[0] = 10;
  test_shift(output, x, y, 64);
  y[1] = 2;
  test_shift(output, x, y, 64);
  return yices_thread_exit();
}

int main(int argc, char* argv[]) {

  if(argc != 2){
    mt_test_usage(argc, argv);
    return 0;
  } else {
    int32_t nthreads = atoi(argv[1]);

    if(nthreads < 0){
      fprintf(stderr, "thread number must be positive!\n");
      exit(EXIT_FAILURE);
    } else if(nthreads == 0){
      thread_data_t tdata = {0, stdout};
      test_thread(&tdata);
    } else {
      launch_threads(nthreads, NULL, 0, "test_bvconst_shifts_mt", test_thread, true);
    }

  }

  return 0;
}

