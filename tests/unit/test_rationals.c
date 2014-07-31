/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of rational functions
 */

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <inttypes.h>
#include <gmp.h>

#include "terms/rationals.h"
#include "terms/mpq_aux.h"

#define MAX_NUMERATOR (INT32_MAX>>1)
#define MIN_NUMERATOR (-MAX_NUMERATOR)
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

static rational_t r0, r1, r2;
static mpq_t q0, q1, q2;


/*
 * Tests
 */
static void q_export(rational_t *r, mpq_t q) {
  if (r->den == 0) {
    mpq_set(q, bank_q[r->num]);
  } else {
    mpq_set_int32(q, r->num, r->den);
  }
}

static void q_check_equal(rational_t *r, mpq_t q) {
  int32_t equal;
  if (r->den == 0) {
    equal = mpq_equal(bank_q[r->num], q);
  } else {
    equal = (mpq_cmp_si(q, r->num, r->den) == 0);
  }
  if (! equal) {
    printf("q_check_error\n");
    printf("  r = ");
    q_print(stdout, r);
    printf("\n");
    printf("  q = ");
    mpq_out_str(stdout, 10, q);
    printf("\n");
    fflush(stdout);
    abort();
  }
}


static void test_equal(rational_t *r, mpq_t q) {
  //  printf("  r = "); q_print(stdout, r); printf("\n");
  //  printf("  q = "); mpq_out_str(stdout, 10, q); printf("\n");
  //  fflush(stdout);
  q_check_equal(r, q);
}

// set r0 = num/den
static void test_assign(int32_t num, uint32_t den) {
  q_set_int32(&r0, num, den);
  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  printf("test assign: %"PRId32"/%"PRIu32"\n", num, den);
  test_equal(&r0, q0);
}

// compute r0 = r1 + num/den
static void test_add(int32_t num, uint32_t den) {
  q_set_int32(&r0, num, den);
  q_add(&r0, &r1);
  printf("test add: %"PRId32"/%"PRIu32" + ", num, den);
  q_print(stdout, &r1);
  printf(" = ");
  q_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_add(q0, q0, q1);
  test_equal(&r0, q0);
}



// compute r0 = num/den - r1
static void test_sub(int32_t num, uint32_t den) {
  q_set_int32(&r0, num, den);
  q_sub(&r0, &r1);
  printf("test sub: %"PRId32"/%"PRIu32" - ", num, den);
  q_print(stdout, &r1);
  printf(" = ");
  q_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_sub(q0, q0, q1);
  test_equal(&r0, q0);
}

// compute r0 = r1 - num/den
static void test_sub2(int32_t num, uint32_t den) {
  q_set(&r0, &r1);
  q_set_int32(&r2, num, den);
  q_sub(&r0, &r2);
  printf("test sub2: ");
  q_print(stdout, &r1);
  printf(" - %"PRId32"/%"PRIu32" = ", num, den);
  q_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_sub(q0, q1, q0);
  test_equal(&r0, q0);
}



// r0 = num/den * r1
static void test_mul(int32_t num, uint32_t den) {
  q_set_int32(&r0, num, den);
  q_mul(&r0, &r1);
  printf("test mul: %"PRId32"/%"PRIu32" * ", num, den);
  q_print(stdout, &r1);
  printf(" = ");
  q_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_mul(q0, q0, q1);
  test_equal(&r0, q0);
}

// r0 = (num/den) / r1
static void test_div(int32_t num, uint32_t den) {
  q_set_int32(&r0, num, den);
  q_div(&r0, &r1);
  printf("test div: (%"PRId32"/%"PRIu32") / ", num, den);
  q_print(stdout, &r1);
  printf(" = ");
  q_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_div(q0, q0, q1);
  test_equal(&r0, q0);
}

// r0 = r1 / (num/den)
static void test_div2(int32_t num, uint32_t den) {
  q_set(&r0, &r1);
  q_set_int32(&r2, num, den);
  q_div(&r0, &r2);
  printf("test div: ");
  q_print(stdout, &r1);
  printf(" / (%"PRId32"/%"PRIu32") = ", num, den);
  q_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_div(q0, q1, q0);
  test_equal(&r0, q0);
}

// r0 = (num1/den1) + r1 * (num2/den2)
static void test_addmul(int32_t num1, uint32_t den1, int32_t num2, uint32_t den2) {
  q_set_int32(&r0, num1, den1);
  q_set_int32(&r2, num2, den2);
  q_addmul(&r0, &r1, &r2);
  printf("test_addmul: %"PRId32"/%"PRIu32" + ", num1, den1);
  q_print(stdout, &r1);
  printf(" * %"PRId32"/%"PRIu32" = ", num2, den2);
  q_print(stdout, &r0);
  printf("\n");

  mpq_set_si(q0, num1, den1);
  mpq_canonicalize(q0);
  mpq_set_si(q2, num2, den2);
  mpq_canonicalize(q2);
  q_export(&r1, q1);
  mpq_mul(q1, q1, q2);
  mpq_add(q0, q0, q1);
  test_equal(&r0, q0);
}



static void assignment_tests() {
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

  q_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      test_add(a, b);
    }
  }
}

static void addition_tests() {
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

  q_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      test_sub(a, b);
      test_sub2(a, b);
    }
  }
}

static void subtraction_tests() {
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

  q_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      test_mul(a, b);
    }
  }
}

static void product_tests() {
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

  q_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      if (num1 != 0) test_div(a, b);
      if (a != 0) test_div2(a, b);
    }
  }
}

static void division_tests() {
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

  q_set_int32(&r1, num1, den1);
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

static void addmul_tests() {
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



int main() {
  int32_t i;

  init_rationals();
  printf("GMP %s (bits per limb = %"PRId32")\n", gmp_version, GMP_LIMB_BITS);
  printf("MAX_NUM = %d\n", MAX_NUMERATOR);
  printf("MIN_NUM = %d\n", MIN_NUMERATOR);
  printf("MAX_DEN = %d\n", MAX_DENOMINATOR);
  printf("----\n\n");

  mpq_init(q0);
  mpq_init(q1);
  mpq_init(q2);
  q_init(&r0);
  q_init(&r1);
  q_init(&r2);

  assignment_tests();
  addition_tests();
  subtraction_tests();
  product_tests();
  division_tests();
  addmul_tests();

  q_set_int32(&r0, MIN_NUMERATOR-1, 23);
  printf("r0 = ");
  q_print(stdout, &r0);
  printf("\n");
  printf("hash num = %"PRIu32"\n", q_hash_numerator(&r0));
  printf("hash den = %"PRIu32"\n", q_hash_denominator(&r0));

  mpq_set_int32(q0, MIN_NUMERATOR-1, 23);
  mpq_canonicalize(q0);
  q_set_mpq(&r1, q0);
  printf("r1 = ");
  q_print(stdout, &r1);
  printf("\n");
  printf("hash num = %"PRIu32"\n", q_hash_numerator(&r1));
  printf("hash den = %"PRIu32"\n", q_hash_denominator(&r1));


  printf("\n\n");
  for (i=0; i<12; i++) {
    printf("set_from_string <%s>\n", test_strings[i]);
    if (q_set_from_string(&r2, test_strings[i]) >= 0) {
      printf("r2 = ");
      q_print(stdout, &r2);
    } else {
      printf("format error\n");
      printf("r2 = ");
      q_print(stdout, &r2);
    }
    printf("\n\n");
  }

  printf("\n");
  for (i=0; i<22; i++) {
    printf("set_from_float_string <%s>\n", test_strings2[i]);
    if (q_set_from_float_string(&r2, test_strings2[i]) >= 0) {
      printf("r2 = ");
      q_print(stdout, &r2);
    } else {
      printf("format error\n");
      printf("r2 = ");
      q_print(stdout, &r2);
    }
    printf("\n\n");
  }

  cleanup_rationals();
  mpq_clear(q0);
  mpq_clear(q1);
  mpq_clear(q2);

  return 0;
}
