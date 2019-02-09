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
 * Test of conversions between rationals and integers
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "terms/neorationals.h"

#define MAX_NUMERATOR (INT32_MAX>>1)
#define MIN_NUMERATOR (-MAX_NUMERATOR)
#define MAX_DENOMINATOR MAX_NUMERATOR


/*
 * Convert r1 to a/b
 */
static void convert_int32_test(neorational_t *r1) {
  int32_t a;
  uint32_t b;
  neorational_t check;

  if (neoq_get_int32(r1, &a, &b)) {
    printf("Rational: ");
    neoq_print(stdout, r1);
    printf(" decomposed to %"PRId32"/%"PRIu32" (32 bits)\n", a, b);
    neoq_init(&check);
    neoq_set_int32(&check, a, b);
    if (! neoq_eq(r1, &check)) {
      printf("---> BUG A MAX_DENOMINATOR = %"PRIu32"\n", MAX_DENOMINATOR);
      neoq_print(stdout, &check);
      printf("\n");
      printf("neoq_cmp(r1, &check) = %d\n", neoq_cmp(r1, &check));
      fflush(stdout);
      exit(1);
    }
    if (! neoq_fits_int32(r1)) {
      printf("---> BUG B\n");
      fflush(stdout);
      exit(1);
    }
    neoq_clear(&check);
  } else {
    printf("Rational: ");
    neoq_print(stdout, r1);
    printf(" not convertible to 32bit integers\n");
    if (neoq_fits_int32(r1)) {
      printf("---> BUG C\n");
      fflush(stdout);
      exit(1);
    }
  }
}


static void convert_int64_test(neorational_t *r1) {
  int64_t a;
  uint64_t b;
  neorational_t check;

  if (neoq_get_int64(r1, &a, &b)) {
    printf("Rational: ");
    neoq_print(stdout, r1);
    printf(" decomposed to %"PRId64"/%"PRIu64" (64 bits)\n", a, b);
    neoq_init(&check);
    neoq_set_int64(&check, a, b);
    if (! neoq_eq(r1, &check)) {
      printf("---> BUG A\n");
      neoq_print(stdout, &check);
      printf("\n");
      printf("neoq_cmp(r1, &check) = %d\n", neoq_cmp(r1, &check));
      fflush(stdout);
      exit(1);
    }
    if (! neoq_fits_int64(r1)) {
      printf("---> BUG B\n");
      fflush(stdout);
      exit(1);
    }
    neoq_clear(&check);
  } else {
    printf("Rational: ");
    neoq_print(stdout, r1);
    printf(" not convertible to 64bit integers\n");
    if (neoq_fits_int64(r1)) {
      printf("---> BUG C\n");
      fflush(stdout);
      exit(1);
    }
  }
}


/*
 * Conversion to an integer
 */
static void convert32_test(neorational_t *r1) {
  int32_t a;
  neorational_t check;

  if (neoq_get32(r1, &a)) {
    printf("Rational: ");
    neoq_print(stdout, r1);
    printf(" equal to %"PRId32" (32 bits)\n", a);
    neoq_init(&check);
    neoq_set32(&check, a);
    if (! neoq_eq(r1, &check)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    if (! neoq_is_int32(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    neoq_clear(&check);
  } else {
    printf("Rational: ");
    neoq_print(stdout, r1);
    printf(" not convertible to a 32bit integer\n");
    if (neoq_is_int32(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
  }
}


static void convert64_test(neorational_t *r1) {
  int64_t a;
  neorational_t check;

  if (neoq_get64(r1, &a)) {
    printf("Rational: ");
    neoq_print(stdout, r1);
    printf(" equal to %"PRId64" (64 bits)\n", a);
    neoq_init(&check);
    neoq_set64(&check, a);
    if (! neoq_eq(r1, &check)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    if (! neoq_is_int64(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
    neoq_clear(&check);
  } else {
    printf("Rational: ");
    neoq_print(stdout, r1);
    printf(" not convertible to a 64bit integer\n");
    if (neoq_is_int64(r1)) {
      printf("---> BUG\n");
      fflush(stdout);
      exit(1);
    }
  }
}


/*
 * Run all conversion tests on r
 */
static void test_conversions(neorational_t *r) {
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
  neorational_t r, aux;
  uint32_t i;

  printf("\nTest 1\n\n");

  neoq_init(&r);
  neoq_init(&aux);
  neoq_set32(&aux, 2);

  neoq_set_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
    neoq_mul(&r, &aux);
  }

  // negative powers
  neoq_set_minus_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
    neoq_mul(&r, &aux);
  }

  neoq_clear(&aux);
  neoq_clear(&r);
}



/*
 * Test2: construct (powers of two) - 1
 */
static void test2(void) {
  neorational_t r, aux, aux2;
  uint32_t i;

  printf("\nTest 2\n\n");

  neoq_init(&r);
  neoq_init(&aux);
  neoq_init(&aux2);
  neoq_set32(&aux, 2);
  neoq_set_one(&aux2);

  neoq_clear(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
    neoq_mul(&r, &aux);
    neoq_add(&r, &aux2);
  }

  neoq_clear(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
    neoq_mul(&r, &aux);
    neoq_sub(&r, &aux2);
  }

  neoq_clear(&aux);
  neoq_clear(&aux2);
  neoq_clear(&r);
}


/*
 * Test 3: inverses of powers of two
 */
static void test3(void) {
  neorational_t r, aux;
  uint32_t i;

  printf("\nTest 3\n\n");

  neoq_init(&r);
  neoq_init(&aux);
  neoq_set_int32(&aux, 1, 2); // 1/2

  neoq_set_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
    neoq_mul(&r, &aux);
  }

  neoq_set_minus_one(&r);
  for (i=0; i<68; i++) {
    test_conversions(&r);
    neoq_mul(&r, &aux);
  }

  neoq_clear(&aux);
  neoq_clear(&r);
}


/*
 * Test 4: construct 1/(2^n-1)
 */
static void test4(void) {
  neorational_t r, aux, aux2;
  uint32_t i;

  printf("\nTest 4\n\n");

  neoq_init(&r);
  neoq_init(&aux);
  neoq_init(&aux2);
  neoq_set32(&aux, 2);
  neoq_set_one(&aux2);

  neoq_set_one(&r);
  for (i=0; i<68; i++) {
    neoq_inv(&r);
    test_conversions(&r);
    neoq_inv(&r);
    neoq_mul(&r, &aux);
    neoq_add(&r, &aux2);
  }

  neoq_set_minus_one(&r);
  for (i=0; i<68; i++) {
    neoq_inv(&r);
    test_conversions(&r);
    neoq_inv(&r);
    neoq_mul(&r, &aux);
    neoq_sub(&r, &aux2);
  }

  neoq_clear(&aux);
  neoq_clear(&aux2);
  neoq_clear(&r);
}


int main(void) {

  init_neorationals();


  test1();
  test2();
  test3();
  test4();

  cleanup_neorationals();

  
  return 0;
}
