/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of conversions between rationals and integers
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "terms/rationals.h"


/*
 * Convert r1 to a/b
 */
static void convert_int32_test(rational_t *r1) {
  int32_t a;
  uint32_t b;
  rational_t check;

  if (q_get_int32(r1, &a, &b)) {
    printf("Rational: ");
    q_print(stdout, r1);
    printf(" decomposed to %"PRId32"/%"PRIu32" (32 bits)\n", a, b);
    q_init(&check);
    q_set_int32(&check, a, b);
    if (! q_eq(r1, &check)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    if (! q_fits_int32(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    q_clear(&check);
  } else {
    printf("Rational: ");
    q_print(stdout, r1);
    printf(" not convertible to 32bit integers\n");
    if (q_fits_int32(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
  }
}


static void convert_int64_test(rational_t *r1) {
  int64_t a;
  uint64_t b;
  rational_t check;

  if (q_get_int64(r1, &a, &b)) {
    printf("Rational: ");
    q_print(stdout, r1);
    printf(" decomposed to %"PRId64"/%"PRIu64" (64 bits)\n", a, b);
    q_init(&check);
    q_set_int64(&check, a, b);
    if (! q_eq(r1, &check)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    if (! q_fits_int64(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    q_clear(&check);
  } else {
    printf("Rational: ");
    q_print(stdout, r1);
    printf(" not convertible to 64bit integers\n");
    if (q_fits_int64(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
  }
}


/*
 * Conversion to an integer
 */
static void convert32_test(rational_t *r1) {
  int32_t a;
  rational_t check;

  if (q_get32(r1, &a)) {
    printf("Rational: ");
    q_print(stdout, r1);
    printf(" equal to %"PRId32" (32 bits)\n", a);
    q_init(&check);
    q_set32(&check, a);
    if (! q_eq(r1, &check)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    if (! q_is_int32(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    q_clear(&check);
  } else {
    printf("Rational: ");
    q_print(stdout, r1);
    printf(" not convertible to a 32bit integer\n");
    if (q_is_int32(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
  }
}


static void convert64_test(rational_t *r1) {
  int64_t a;
  rational_t check;

  if (q_get64(r1, &a)) {
    printf("Rational: ");
    q_print(stdout, r1);
    printf(" equal to %"PRId64" (64 bits)\n", a);
    q_init(&check);
    q_set64(&check, a);
    if (! q_eq(r1, &check)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    if (! q_is_int64(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    q_clear(&check);
  } else {
    printf("Rational: ");
    q_print(stdout, r1);
    printf(" not convertible to a 64bit integer\n");
    if (q_is_int64(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
  }
}


/*
 * Run all conversion tests on r
 */
static void test_conversions(rational_t *r) {
  convert_int32_test(r);
  convert_int64_test(r);
  convert32_test(r);
  convert64_test(r);
  printf("---\n");
}


/*
 * Test1: construct powers of two
 */
static void test1(void) {
  rational_t r, aux;
  uint32_t i;

  printf("\nTest 1\n\n");

  q_init(&r);
  q_init(&aux);
  q_set32(&aux, 2);

  q_set_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
    q_mul(&r, &aux);
  }

  // negative powers
  q_set_minus_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
    q_mul(&r, &aux);
  }

  q_clear(&aux);
  q_clear(&r);
}



/*
 * Test2: construct (powers of two) - 1
 */
static void test2(void) {
  rational_t r, aux, aux2;
  uint32_t i;

  printf("\nTest 2\n\n");

  q_init(&r);
  q_init(&aux);
  q_init(&aux2);
  q_set32(&aux, 2);
  q_set_one(&aux2);

  q_clear(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
    q_mul(&r, &aux);
    q_add(&r, &aux2);
  }

  q_clear(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
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
static void test3(void) {
  rational_t r, aux;
  uint32_t i;

  printf("\nTest 3\n\n");

  q_init(&r);
  q_init(&aux);
  q_set_int32(&aux, 1, 2); // 1/2

  q_set_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
    q_mul(&r, &aux);
  }

  q_set_minus_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
    q_mul(&r, &aux);
  }

  q_clear(&aux);
  q_clear(&r);
}


/*
 * Test 4: construct 1/(2^n-1)
 */
static void test4(void) {
  rational_t r, aux, aux2;
  uint32_t i;

  printf("\nTest 4\n\n");

  q_init(&r);
  q_init(&aux);
  q_init(&aux2);
  q_set32(&aux, 2);
  q_set_one(&aux2);

  q_set_one(&r);
  for (i=0; i<68; i++) {
    q_inv(&r);
    test_conversions(&r);
    q_inv(&r);
    q_mul(&r, &aux);
    q_add(&r, &aux2);
  }

  q_set_minus_one(&r);
  for (i=0; i<68; i++) {
    q_inv(&r);
    test_conversions(&r);
    q_inv(&r);
    q_mul(&r, &aux);
    q_sub(&r, &aux2);
  }

  q_clear(&aux);
  q_clear(&aux2);
  q_clear(&r);
}


int main(void) {
  init_rationals();
  test1();
  test2();
  test3();
  test4();
  cleanup_rationals();
  return 0;
}
