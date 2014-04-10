/*
 * Test of conversions between rationals and integers
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "rationals.h"
#include "threads.h"


/*
 * Convert r1 to a/b
 */
static void convert_int32_test(FILE* output, rational_t *r1) {
  int32_t a;
  uint32_t b;
  rational_t check;

  if (q_get_int32(r1, &a, &b)) {
    fprintf(output, "Rational: ");
    q_print(output, r1);
    fprintf(output, " decomposed to %"PRId32"/%"PRIu32" (32 bits)\n", a, b);
    q_init(&check);
    q_set_int32(&check, a, b);
    if (! q_eq(r1, &check)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
    if (! q_fits_int32(r1)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
    q_clear(&check);
  } else {
    fprintf(output, "Rational: ");
    q_print(output, r1);
    fprintf(output, " not convertible to 32bit integers\n");
    if (q_fits_int32(r1)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
  }
}


static void convert_int64_test(FILE* output, rational_t *r1) {
  int64_t a;
  uint64_t b;
  rational_t check;

  if (q_get_int64(r1, &a, &b)) {
    fprintf(output, "Rational: ");
    q_print(output, r1);
    fprintf(output, " decomposed to %"PRId64"/%"PRIu64" (64 bits)\n", a, b);
    q_init(&check);
    q_set_int64(&check, a, b);
    if (! q_eq(r1, &check)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
    if (! q_fits_int64(r1)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
    q_clear(&check);
  } else {
    fprintf(output, "Rational: ");
    q_print(output, r1);
    fprintf(output, " not convertible to 64bit integers\n");
    if (q_fits_int64(r1)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
  }
}


/*
 * Conversion to an integer
 */
static void convert32_test(FILE* output, rational_t *r1) {
  int32_t a;
  rational_t check;

  if (q_get32(r1, &a)) {
    fprintf(output, "Rational: ");
    q_print(output, r1);
    fprintf(output, " equal to %"PRId32" (32 bits)\n", a);
    q_init(&check);
    q_set32(&check, a);
    if (! q_eq(r1, &check)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
    if (! q_is_int32(r1)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
    q_clear(&check);
  } else {
    fprintf(output, "Rational: ");
    q_print(output, r1);
    fprintf(output, " not convertible to a 32bit integer\n");
    if (q_is_int32(r1)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
  }
}


static void convert64_test(FILE* output, rational_t *r1) {
  int64_t a;
  rational_t check;

  if (q_get64(r1, &a)) {
    fprintf(output, "Rational: ");
    q_print(output, r1);
    fprintf(output, " equal to %"PRId64" (64 bits)\n", a);
    q_init(&check);
    q_set64(&check, a);
    if (! q_eq(r1, &check)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
    if (! q_is_int64(r1)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
    q_clear(&check);
  } else {
    fprintf(output, "Rational: ");
    q_print(output, r1);
    fprintf(output, " not convertible to a 64bit integer\n");
    if (q_is_int64(r1)) {
      fprintf(output, "---> BUG\n");
      fflush(output);
      exit(1);
    }
  }
}


/*
 * Run all conversion tests on r
 */
static void test_conversions(FILE* output, rational_t *r) {
  convert_int32_test(output, r);
  convert_int64_test(output, r);
  convert32_test(output, r);
  convert64_test(output, r);
  fprintf(output, "---\n");
}


/*
 * Test1: construct powers of two
 */
static void test1(FILE* output) {
  rational_t r, aux;
  uint32_t i;

  fprintf(output, "\nTest 1\n\n");

  q_init(&r);
  q_init(&aux);
  q_set32(&aux, 2);

  q_set_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(output, &r);
    q_mul(&r, &aux);
  }

  // negative powers
  q_set_minus_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(output, &r);
    q_mul(&r, &aux);
  }

  q_clear(&aux);
  q_clear(&r);
}



/*
 * Test2: construct (powers of two) - 1
 */
static void test2(FILE* output) {
  rational_t r, aux, aux2;
  uint32_t i;

  fprintf(output, "\nTest 2\n\n");

  q_init(&r);
  q_init(&aux);
  q_init(&aux2);
  q_set32(&aux, 2);
  q_set_one(&aux2);

  q_clear(&r);
  for (i=0; i<68; i++) {
    test_conversions(output, &r);
    q_mul(&r, &aux);
    q_add(&r, &aux2);
  }

  q_clear(&r);
  for (i=0; i<68; i++) {
    test_conversions(output, &r);
    q_mul(&r, &aux);
    q_sub(&r, &aux2);
  }

  q_clear(&aux);
  q_clear(&aux2);
  q_clear(&r);
}


/*
 * Test 3: inverses of powers of two
 */
static void test3(FILE* output) {
  rational_t r, aux;
  uint32_t i;

  fprintf(output, "\nTest 3\n\n");

  q_init(&r);
  q_init(&aux);
  q_set_int32(&aux, 1, 2); // 1/2

  q_set_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(output, &r);
    q_mul(&r, &aux);
  }

  q_set_minus_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(output, &r);
    q_mul(&r, &aux);
  }

  q_clear(&aux);
  q_clear(&r);
}


/*
 * Test 4: construct 1/(2^n-1)
 */
static void test4(FILE* output) {
  rational_t r, aux, aux2;
  uint32_t i;

  fprintf(output, "\nTest 4\n\n");

  q_init(&r);
  q_init(&aux);
  q_init(&aux2);
  q_set32(&aux, 2);
  q_set_one(&aux2);

  q_set_one(&r);
  for (i=0; i<68; i++) {
    q_inv(&r);
    test_conversions(output, &r);
    q_inv(&r);
    q_mul(&r, &aux);
    q_add(&r, &aux2);
  }

  q_set_minus_one(&r);
  for (i=0; i<68; i++) {
    q_inv(&r);
    test_conversions(output, &r);
    q_inv(&r);
    q_mul(&r, &aux);
    q_sub(&r, &aux2);
  }

  q_clear(&aux);
  q_clear(&aux2);
  q_clear(&r);
}

yices_thread_result_t test_thread(void* arg){
  FILE* output = (FILE *)arg;
  fprintf(stderr, "Starting: %s\n", "test1");
  test1(output);
  fprintf(stderr, "Starting: %s\n", "test2");
  test2(output);
  fprintf(stderr, "Starting: %s\n", "test3");
  test3(output);
  fprintf(stderr, "Starting: %s\n", "test4");
  test4(output);
  fprintf(stderr, "Done.\n");
  return NULL;
}

int main(int argc, char* argv[]) {

  if(argc != 2){
    mt_test_usage(argc, argv);
    return 0;
  } else {
    int nthreads = atoi(argv[1]);

    init_rationals();

    if(nthreads < 0){
      fprintf(stderr, "thread number must be positive!\n");
      exit(EXIT_FAILURE);
    } else if(nthreads == 0){
      test_thread(stdout);
    } else {
      launch_threads(nthreads, "/tmp/test_rational_conversions_mt_%d.txt", test_thread);
    }

    cleanup_rationals();

  }
  return 0;
}
