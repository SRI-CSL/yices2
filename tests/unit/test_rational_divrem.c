/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of integer division implemented in rationals.c
 */

#include <stdio.h>
#include <inttypes.h>

#include "terms/rationals.h"


/*
 * Table to initialize large numbers
 */
#define NBIGS 16

static char* large_signed[NBIGS] = {
  "1073741822",
  "1073741823",
  "1073741824",
  "1073741825",
  "-1073741822",
  "-1073741823",
  "-1073741824",
  "-1073741825",
  "3219483903484189430",
  "-321948390344899848",
  "219483903484189430",
  "-21948390344899848",
  "+100000000000",
  "-100000000000",
  "+80000000000000",
  "-80000000000000"
};

// divisors must all be positive
static char* large_divisor[NBIGS] = {
  "1073741822",
  "1073741823",
  "1073741824",
  "1073741825",
  "1073741826",
  "1073741827",
  "1073741828",
  "3219483903484189430",
  "219483903484189430",
  "100000000000",
  "50000000000",
  "20000000000",
  "80000000000000",
  "40000000000000",
  "20000000000000",
  "10000000000000",
};


/*
 * Test 1: a divided by b
 * - both a and b are small integers
 */
static void test_small_small(void) {
  rational_t a, b, c;
  int32_t x, y;

  q_init(&a);
  q_init(&b);
  q_init(&c);

  for (y=1; y<8; y++) {
    q_set32(&b, y);
    for (x=-20; x<=20; x++) {
      q_set32(&a, x);
      q_integer_div(&a, &b);
      q_set32(&c, x);
      q_integer_rem(&c, &b);

      printf("div[%3"PRId32", %"PRId32"]: quotient = ", x, y);
      q_print(stdout, &a);
      printf(", remainder = ");
      q_print(stdout, &c);
      printf("\n");
    }
    printf("\n");
  }

  q_clear(&a);
  q_clear(&b);
  q_clear(&c);
}


/*
 * Test 2: a is large, b is small
 */
static void test_big_small(void) {
  rational_t a, b, c;
  uint32_t i;
  int32_t y;

  q_init(&a);
  q_init(&b);
  q_init(&c);

  for (y=1; y<8; y++) {
    q_set32(&b, y);
    for (i=0; i<NBIGS; i++) {
      q_set_from_string(&a, large_signed[i]);
      q_set(&c, &a);
      q_integer_div(&a, &b);
      q_integer_rem(&c, &b);

      printf("div[%s, %"PRId32"]: quotient = ", large_signed[i], y);
      q_print(stdout, &a);
      printf(", remainder = ");
      q_print(stdout, &c);
      printf("\n");
    }
    printf("\n");
  }

  q_clear(&a);
  q_clear(&b);
  q_clear(&c);
}

/*
 * Test 3: a is small, b is large
 */
static void test_small_big(void) {
  rational_t a, b, c;
  uint32_t i;
  int32_t x;

  q_init(&a);
  q_init(&b);
  q_init(&c);

  for (i=0; i<NBIGS; i++) {
    q_set_from_string(&b, large_divisor[i]);
    for (x=-10; x<=10; x++) {
      q_set32(&a, x);
      q_set32(&c, x);
      q_integer_div(&a, &b);
      q_integer_rem(&c, &b);

      printf("div[%"PRId32", %s]: quotient = ", x, large_divisor[i]);
      q_print(stdout, &a);
      printf(", remainder = ");
      q_print(stdout, &c);
      printf("\n");
    }
    printf("\n");
  }

  q_clear(&a);
  q_clear(&b);
  q_clear(&c);
}


/*
 * Test 4: a is large, b is large
 */
static void test_big_big(void) {
  rational_t a, b, c;
  uint32_t i, j;

  q_init(&a);
  q_init(&b);
  q_init(&c);

  for (i=0; i<NBIGS; i++) {
    q_set_from_string(&b, large_divisor[i]);
    for (j=0; j<NBIGS; j++) {
      q_set_from_string(&a, large_signed[j]);
      q_set(&c, &a);
      q_integer_div(&a, &b);
      q_integer_rem(&c, &b);

      printf("div[%s, %s]: quotient = ", large_signed[j], large_divisor[i]);
      q_print(stdout, &a);
      printf(", remainder = ");
      q_print(stdout, &c);
      printf("\n");
    }
    printf("\n");
  }

  q_clear(&a);
  q_clear(&b);
  q_clear(&c);
}

int main() {
  init_rationals();
  test_small_small();
  test_big_small();
  test_small_big();
  test_big_big();
  cleanup_rationals();
  return 0;
}
