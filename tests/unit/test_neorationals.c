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
 * Test of rational functions
 */

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <inttypes.h>
#include <gmp.h>

#include "terms/mpq_aux.h"
#include "terms/neorationals.h"

#define MAX_NUMERATOR (INT32_MAX>>1)
#define MIN_NUMERATOR (-MAX_NUMERATOR)
//IAM: leave this alone here.
#define MAX_DENOMINATOR MAX_NUMERATOR


static int32_t num[24] = {
  0, 1, -1, -23, 23,
  112, -112, 126, -126, INT32_MAX,
  INT32_MIN, MAX_NUMERATOR, MIN_NUMERATOR, MAX_NUMERATOR - 1, MIN_NUMERATOR + 1,
  MAX_NUMERATOR + 1, MIN_NUMERATOR - 1, MAX_NUMERATOR + 2, MIN_NUMERATOR - 2,
  INT32_MAX-1, INT32_MIN + 1, 100, 1000, 10000,
};

static uint32_t den[16] = {
  1, 100, 1000, 10000, 126, 112, 23, 25, UINT32_MAX,
  INT32_MAX, INT32_MAX - 1, ((uint32_t) INT32_MAX) + 1, ((uint32_t) INT32_MAX) + 2,
  MAX_DENOMINATOR, MAX_DENOMINATOR - 1, MAX_DENOMINATOR + 1,
};

static char* test_strings[12] = {
  "1/10", "+1/10", "-1/10",
  "1889139832988/137873278932897", "8eeee/8792183jeebag",
  "00001893821/000031278781238", "",
  "+11398990", "-1893983982", "819230982139",
  "46878952/46878952", "-46878952/46878952",
};

static char* test_strings2[22] = {
  "1.10", "+1.10", "-1.10",
  "100e0", "100e-2", "100e+2",
  "10.6e0", "10.6e-2", "10.6e+2",
  "+10.6e0", "+10.6e-2", "+10.6e+2",
  "-10.6e0", "-10.6e-2", "-10.6e+2",
  "1889139832988.137873278932897e-4", "8.eee",
  "00001893821/000031278781238", "",
  "46878952/46878952", "+46878952/46878952", "-46878952/46878952",
};

static neorational_t r0, r1, r2;
static mpq_t q0, q1, q2;


/*
 * Tests
 */
static void neoq_export(neorational_t *r, mpq_t q) {
  if (is_ratgmp(r)) {
    mpq_set(q, *get_gmp(r));
  } else {
    mpq_set_int32(q, r->s.num, get_den(r));
  }
}

static void neoq_check_equal(neorational_t *r, mpq_t q) {
  int32_t equal;
  if (is_ratgmp(r)) {
    equal = mpq_equal(*get_gmp(r), q);
  } else {
    equal = (mpq_cmp_si(q, r->s.num, get_den(r)) == 0);
  }
  if (! equal) {
    printf("neoq_check_error\n");
    printf("  r = ");
    neoq_print(stdout, r);
    printf("\n");
    printf("  q = ");
    mpq_out_str(stdout, 10, q);
    printf("\n");
    fflush(stdout);
    abort();
  }
}


static void test_equal(neorational_t *r, mpq_t q) {
  //  printf("  r = "); q_print(stdout, r); printf("\n");
  //  printf("  q = "); mpq_out_str(stdout, 10, q); printf("\n");
  //  fflush(stdout);
  neoq_check_equal(r, q);
}

// set r0 = num/den
static void test_assign(int32_t num, uint32_t den) {
  neoq_set_int32(&r0, num, den);
  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  printf("test assign: %"PRId32"/%"PRIu32"\n", num, den);
  test_equal(&r0, q0);
}

// compute r0 = r1 + num/den
static void test_add(int32_t num, uint32_t den) {
  neoq_set_int32(&r0, num, den);
  neoq_add(&r0, &r1);
  printf("test add: %"PRId32"/%"PRIu32" + ", num, den);
  neoq_print(stdout, &r1);
  printf(" = ");
  neoq_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  neoq_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_add(q0, q0, q1);
  test_equal(&r0, q0);
}



// compute r0 = num/den - r1
static void test_sub(int32_t num, uint32_t den) {
  neoq_set_int32(&r0, num, den);
  neoq_sub(&r0, &r1);
  printf("test sub: %"PRId32"/%"PRIu32" - ", num, den);
  neoq_print(stdout, &r1);
  printf(" = ");
  neoq_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  neoq_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_sub(q0, q0, q1);
  test_equal(&r0, q0);
}

// compute r0 = r1 - num/den
static void test_sub2(int32_t num, uint32_t den) {
  neoq_set(&r0, &r1);
  neoq_set_int32(&r2, num, den);
  neoq_sub(&r0, &r2);
  printf("test sub2: ");
  neoq_print(stdout, &r1);
  printf(" - %"PRId32"/%"PRIu32" = ", num, den);
  neoq_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  neoq_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_sub(q0, q1, q0);
  test_equal(&r0, q0);
}



// r0 = num/den * r1
static void test_mul(int32_t num, uint32_t den) {
  neoq_set_int32(&r0, num, den);
  neoq_mul(&r0, &r1);
  printf("test mul: %"PRId32"/%"PRIu32" * ", num, den);
  neoq_print(stdout, &r1);
  printf(" = ");
  neoq_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  neoq_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_mul(q0, q0, q1);
  test_equal(&r0, q0);
}

// r0 = (num/den) / r1
static void test_div(int32_t num, uint32_t den) {
  neoq_set_int32(&r0, num, den);
  neoq_div(&r0, &r1);
  printf("test div: (%"PRId32"/%"PRIu32") / ", num, den);
  neoq_print(stdout, &r1);
  printf(" = ");
  neoq_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  neoq_export(&r1, q1);
  mpq_div(q0, q0, q1);
  test_equal(&r0, q0);
}

// r0 = r1 / (num/den)
static void test_div2(int32_t num, uint32_t den) {
  neoq_set(&r0, &r1);
  neoq_set_int32(&r2, num, den);
  neoq_div(&r0, &r2);
  printf("test div: ");
  neoq_print(stdout, &r1);
  printf(" / (%"PRId32"/%"PRIu32") = ", num, den);
  neoq_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  neoq_export(&r1, q1);
  mpq_div(q0, q1, q0);
  test_equal(&r0, q0);
}

// r0 = (num1/den1) + r1 * (num2/den2)
static void test_addmul(int32_t num1, uint32_t den1, int32_t num2, uint32_t den2) {
  neoq_set_int32(&r0, num1, den1);
  neoq_set_int32(&r2, num2, den2);
  neoq_addmul(&r0, &r1, &r2);
  printf("test_addmul: %"PRId32"/%"PRIu32" + ", num1, den1);
  neoq_print(stdout, &r1);
  printf(" * %"PRId32"/%"PRIu32" = ", num2, den2);
  neoq_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num1, den1);
  mpq_canonicalize(q0);
  mpq_set_si(q2, num2, den2);
  mpq_canonicalize(q2);
  neoq_export(&r1, q1);
  mpq_mul(q1, q1, q2);
  mpq_add(q0, q0, q1);
  test_equal(&r0, q0);
}



static void assignment_tests(void) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      test_assign(a, b);
    }
  }
}

static void addition_test(int32_t num1, uint32_t den1) {
  int32_t i, j, a;
  uint32_t b;

  neoq_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      test_add(a, b);
    }
  }
}

static void addition_tests(void) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      addition_test(a, b);
    }
  }
}

static void subtraction_test(int32_t num1, uint32_t den1) {
  int32_t i, j, a;
  uint32_t b;

  neoq_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      test_sub(a, b);
      test_sub2(a, b);
    }
  }
}

static void subtraction_tests(void) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      subtraction_test(a, b);
    }
  }
}




static void product_test(int32_t num1, uint32_t den1) {
  int32_t i, j, a;
  uint32_t b;

  neoq_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      test_mul(a, b);
    }
  }
}

static void product_tests(void) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      product_test(a, b);
    }
  }
}

static void division_test(int32_t num1, uint32_t den1) {
  int32_t i, j, a;
  uint32_t b;

  neoq_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      if (num1 != 0) test_div(a, b);
      if (a != 0) test_div2(a, b);
    }
  }
}

static void division_tests(void) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      division_test(a, b);
    }
  }
}

static void addmul_test(int32_t num1, uint32_t den1) {
  int32_t i, j, a, b;
  uint32_t c, d;

  neoq_set_int32(&r1, num1, den1);
  for (i=0; i<15; i++) {
    c = den[i];
    d = den[i+1];
    for (j=0; j<23; j++) {
      a = num[j];
      b = num[j+1];
      test_addmul(a, c, b, d);
    }
  }
}

static void addmul_tests(void) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      addmul_test(a, b);
    }
  }

}



int main(void) {
  int32_t i;

  printf("GMP %s (bits per limb = %"PRId32")\n", gmp_version, GMP_LIMB_BITS);
  printf("MAX_NUM = %d\n", MAX_NUMERATOR);
  printf("MIN_NUM = %d\n", MIN_NUMERATOR);
  printf("MAX_DEN = %d\n", MAX_DENOMINATOR);
  printf("----\n\n");
  init_neorationals();

  mpq_init(q0);
  mpq_init(q1);
  mpq_init(q2);
  neoq_init(&r0);
  neoq_init(&r1);
  neoq_init(&r2);

  assignment_tests();
  addition_tests();
  subtraction_tests();
  product_tests();
  division_tests();
  addmul_tests();

  neoq_set_int32(&r0, MIN_NUMERATOR-1, 23);
  printf("r0 = ");
  neoq_print(stdout, &r0);
  printf("\n");
  printf("hash num = %"PRIu32"\n", neoq_hash_numerator(&r0));
  printf("hash den = %"PRIu32"\n", neoq_hash_denominator(&r0));

  mpq_set_int32(q0, MIN_NUMERATOR-1, 23);
  mpq_canonicalize(q0);
  neoq_set_mpq(&r1, q0);
  printf("r1 = ");
  neoq_print(stdout, &r1);
  printf("\n");
  printf("hash num = %"PRIu32"\n", neoq_hash_numerator(&r1));
  printf("hash den = %"PRIu32"\n", neoq_hash_denominator(&r1));


  printf("\n\n");
  for (i=0; i<12; i++) {
    printf("set_from_string <%s>\n", test_strings[i]);
    if (neoq_set_from_string(&r2, test_strings[i]) >= 0) {
      printf("r2 = ");
      neoq_print(stdout, &r2);
    } else {
      printf("format error\n");
      printf("r2 = ");
      neoq_print(stdout, &r2);
    }
    printf("\n\n");
  }

  printf("\n");
  for (i=0; i<22; i++) {
    printf("set_from_float_string <%s>\n", test_strings2[i]);
    if (neoq_set_from_float_string(&r2, test_strings2[i]) >= 0) {
      printf("r2 = ");
      neoq_print(stdout, &r2);
    } else {
      printf("format error\n");
      printf("r2 = ");
      neoq_print(stdout, &r2);
    }
    printf("\n\n");
  }

  mpq_clear(q0);
  mpq_clear(q1);
  mpq_clear(q2);
  neoq_clear(&r0);
  neoq_clear(&r1);
  neoq_clear(&r2);

  cleanup_neorationals();

  return 0;
}
