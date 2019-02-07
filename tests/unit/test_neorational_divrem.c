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
 * Test of integer division implemented in rationals.c
 */

#include <stdio.h>
#include <inttypes.h>

#include "terms/neorationals.h"


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
  neorational_t a, b, c;
  int32_t x, y;

  neoq_init(&a);
  neoq_init(&b);
  neoq_init(&c);

  for (y=1; y<8; y++) {
    neoq_set32(&b, y);
    for (x=-20; x<=20; x++) {
      neoq_set32(&a, x);
      neoq_integer_div(&a, &b);
      neoq_set32(&c, x);
      neoq_integer_rem(&c, &b);

      printf("div[%3"PRId32", %"PRId32"]: quotient = ", x, y);
      neoq_print(stdout, &a);
      printf(", remainder = ");
      neoq_print(stdout, &c);
      printf("\n");
    }
    printf("\n");
  }

  neoq_clear(&a);
  neoq_clear(&b);
  neoq_clear(&c);
}


/*
 * Test 2: a is large, b is small
 */
static void test_big_small(void) {
  neorational_t a, b, c;
  uint32_t i;
  int32_t y;

  neoq_init(&a);
  neoq_init(&b);
  neoq_init(&c);

  for (y=1; y<8; y++) {
    neoq_set32(&b, y);
    for (i=0; i<NBIGS; i++) {
      neoq_set_from_string(&a, large_signed[i]);
      neoq_set(&c, &a);
      neoq_integer_div(&a, &b);
      neoq_integer_rem(&c, &b);

      printf("div[%s, %"PRId32"]: quotient = ", large_signed[i], y);
      neoq_print(stdout, &a);
      printf(", remainder = ");
      neoq_print(stdout, &c);
      printf("\n");
    }
    printf("\n");
  }

  neoq_clear(&a);
  neoq_clear(&b);
  neoq_clear(&c);
}

/*
 * Test 3: a is small, b is large
 */
static void test_small_big(void) {
  neorational_t a, b, c;
  uint32_t i;
  int32_t x;

  neoq_init(&a);
  neoq_init(&b);
  neoq_init(&c);

  for (i=0; i<NBIGS; i++) {
    neoq_set_from_string(&b, large_divisor[i]);
    for (x=-10; x<=10; x++) {
      neoq_set32(&a, x);
      neoq_set32(&c, x);
      neoq_integer_div(&a, &b);
      neoq_integer_rem(&c, &b);

      printf("div[%"PRId32", %s]: quotient = ", x, large_divisor[i]);
      neoq_print(stdout, &a);
      printf(", remainder = ");
      neoq_print(stdout, &c);
      printf("\n");
    }
    printf("\n");
  }

  neoq_clear(&a);
  neoq_clear(&b);
  neoq_clear(&c);
}


/*
 * Test 4: a is large, b is large
 */
static void test_big_big(void) {
  neorational_t a, b, c;
  uint32_t i, j;

  neoq_init(&a);
  neoq_init(&b);
  neoq_init(&c);

  for (i=0; i<NBIGS; i++) {
    neoq_set_from_string(&b, large_divisor[i]);
    for (j=0; j<NBIGS; j++) {
      neoq_set_from_string(&a, large_signed[j]);
      neoq_set(&c, &a);
      neoq_integer_div(&a, &b);
      neoq_integer_rem(&c, &b);

      printf("div[%s, %s]: quotient = ", large_signed[j], large_divisor[i]);
      neoq_print(stdout, &a);
      printf(", remainder = ");
      neoq_print(stdout, &c);
      printf("\n");
    }
    printf("\n");
  }

  neoq_clear(&a);
  neoq_clear(&b);
  neoq_clear(&c);
}

int main(void) {

  init_neorationals();

  test_small_small();
  test_big_small();
  test_small_big();
  test_big_big();

  cleanup_neorationals();


 return 0;
}
