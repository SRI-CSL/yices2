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

#include <assert.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "terms/bv64_constants.h"
#include "terms/bv64_interval_abstraction.h"


/*
 * PRINT
 */

// convert sign to a string into buffer aux
static void sign2string(char aux[30], int32_t sign) {
  switch (sign) {
  case sign_undef:
    strcpy(aux, "undef");
    break;

  case sign_zero:
    strcpy(aux, "zero");
    break;

  case sign_one:
    strcpy(aux, "one");
    break;

  default:
    assert(sign >= 0);
    if ((sign & 1) == 0) {
      snprintf(aux, 30, "p!%"PRId32, (sign >> 1));
    } else {
      snprintf(aux, 30, "~p!%"PRId32, (sign >> 1));
    }
    break;
  } 
}

static void show_interval(FILE *f, const bv64_abs_t *a) {
  char aux[30];

  sign2string(aux, a->sign);
  fprintf(f, "[%"PRId64", %"PRId64"] (%"PRIu32" bits, sign = %s)\n",
	  a->low, a->high, a->nbits, aux);
}



/*
 * INTERVAL CONSTRUCTION
 */

/*
 * Number of significant bits in x
 * - if the result is k then -2^(k-1) <= x < 2^(k-1)
 */
static uint32_t num_significant_bits(int64_t x) {
  int64_t low, high;
  uint32_t k;

  low = INT64_MIN/2;
  high = -low;
  k = 64;
  while (low <= x && x < high) {
    low /= 2;
    high /= 2;
    k --;
  }
  return k;
}


/*
 * Number of bits to represent the interval [low, high]
 */
static uint32_t interval_bitsize(int64_t low, int64_t high) {
  uint32_t kl, kh;

  kl = num_significant_bits(low);
  kh = num_significant_bits(high);
  return (kl < kh) ? kh : kl;
}


/*
 * Sign for the interval [low, high] if known or s otherwise
 */
static int32_t interval_sign(int64_t low, int64_t high, int32_t s) {
  if (low >= 0) {
    s = sign_zero;
  } else if (high < 0) {
    s = sign_one;
  }
  return s;
}

/*
 * Make interval [low, high]
 * - if low < 0 <= high, then s is used as sign for a
 * - otherwise the sign is either sign_zero or sign_one
 */
static void make_interval(bv64_abs_t *a, int64_t low, int64_t high, int32_t s) {
  assert(low <= high);

  a->nbits = interval_bitsize(low, high);
  a->sign = interval_sign(low, high, s);
  a->low = low;
  a->high = high;
}


// min integer = -2^(k-1)
static inline int64_t min_int(uint32_t k) {
  assert(1 <= k && k <= 64);
  return - (int64_t)(((uint64_t) 1) << (k -1));
}

// max integer = 2^(k-1) - 1
static inline int64_t max_int(uint32_t k) {
  assert(1 <= k && k <= 64);
  return (int64_t)((((uint64_t) 1) << (k -1)) - 1);
}


/*
 * Create a set of intervals for bitvectors of n bits
 * - store them in array a
 * - n must be at least 4
 * - this creates 30 intervals
 */
static void make_interval_set(bv64_abs_t a[30], uint32_t n) {
  int64_t min, max;

  assert(n >= 4 && n <= 64);

  min = min_int(n);
  max = max_int(n);

  // point intervals
  make_interval(a, 0, 0, sign_undef);
  make_interval(a+1, 1, 1, sign_undef);
  make_interval(a+2, -1, -1, sign_undef);
  make_interval(a+3, min, min, sign_undef);
  make_interval(a+4, max, max, sign_undef);

  // positive/negative halves
  make_interval(a+5, min, -1, sign_undef);
  make_interval(a+6, 0, max, sign_undef);  
  make_interval(a+7, 1, max, sign_undef);  // all elements strictly positive

  // smaller positive/negative intervals
  make_interval(a+8, min/2, -1, sign_undef);
  make_interval(a+9, 0, max/2, sign_undef);
  make_interval(a+10, 1, max/2, sign_undef);

  // intervals with positive and negative elements
  // for each we set the sign bit to undef then to some literal
  make_interval(a+11, min, max, sign_undef);
  make_interval(a+12, min, max, 2);
  make_interval(a+13, min, max, 0x2^1); // flip the sign
  make_interval(a+14, min, max, 6);

  make_interval(a+15, min/2, 2, sign_undef);
  make_interval(a+16, min/2, 2, 2);
  make_interval(a+17, min/2, 2, 0x2^1);
  make_interval(a+17, min/2, 2, 8);

  make_interval(a+18, -4, 5, sign_undef);
  make_interval(a+19, -4, 5, 2);
  make_interval(a+20, -4, 5, 0x2^1);
  make_interval(a+21, -4, 5, 10);

  make_interval(a+22, -5, 4, sign_undef);
  make_interval(a+23, -5, 4, 2);
  make_interval(a+24, -5, 4, 0x2^1);
  make_interval(a+25, -5, 4, 10);

  // corner cases: max is 0
  make_interval(a+26, -7, 0, sign_undef);
  make_interval(a+27, -7, 0, 2);
  make_interval(a+28, -7, 0, 0x2^1);
  make_interval(a+29, -7, 0, 10);
}



/*
 * BASIC TESTS
 */
static void test_negate(const bv64_abs_t *a) {
  bv64_abs_t aux;

  printf("test negate:\n");
  printf("  input = ");
  show_interval(stdout, a);
  aux = *a;
  bv64_abs_negate(&aux);
  printf("  result = ");
  show_interval(stdout, &aux);
}

static void test_add(const bv64_abs_t *a, const bv64_abs_t *b) {
  bv64_abs_t aux;

  printf("test add:\n");
  printf("  input1 = ");
  show_interval(stdout, a);
  printf("  input2 = ");
  show_interval(stdout, b);

  aux = *a;
  bv64_abs_add(&aux, b);
  printf("  result = ");
  show_interval(stdout, &aux);
}

static void test_sub(const bv64_abs_t *a, const bv64_abs_t *b) {
  bv64_abs_t aux;

  printf("test sub:\n");
  printf("  input1 = ");
  show_interval(stdout, a);
  printf("  input2 = ");
  show_interval(stdout, b);

  aux = *a;
  bv64_abs_sub(&aux, b);
  printf("  result = ");
  show_interval(stdout, &aux);
}

static void test_mul(const bv64_abs_t *a, const bv64_abs_t *b) {
  bv64_abs_t aux;

  printf("test mul:\n");
  printf("  input1 = ");
  show_interval(stdout, a);
  printf("  input2 = ");
  show_interval(stdout, b);

  aux = *a;
  bv64_abs_mul(&aux, b);
  printf("  result = ");
  show_interval(stdout, &aux);
}

static void test_power(const bv64_abs_t *a, uint32_t d) {
  bv64_abs_t aux;

  printf("test power:\n");
  printf("  input = ");
  show_interval(stdout, a);
  printf("  exponent = %"PRIu32"\n", d);

  aux = *a;
  bv64_abs_power(&aux, d);
  printf("  result = ");
  show_interval(stdout, &aux);
}


/*
 * Run tests for all elements of array a
 * - n = size of a
 */
static void run_tests(const bv64_abs_t *a, uint32_t n) {
  uint32_t i, j;

  for (i=0; i<n; i++) {
    test_negate(a+i);
  }

  printf("\n");
  for (i=0; i<n; i++) {
    for (j=0; j<n; j++) {
      test_add(a+i, a+j);
    }
  }

  printf("\n");
  for (i=0; i<n; i++) {
    for (j=0; j<n; j++) {
      test_sub(a+i, a+j);
    }
  }

  printf("\n");
  for (i=0; i<n; i++) {
    for (j=0; j<n; j++) {
      test_mul(a+i, a+j);
    }
  }

  printf("\n");
  for (i=0; i<n; i++) {
    for (j=0; j<7; j++) {
      test_power(a+i, j);
    }
  }
}


/*
 * Global array for testing
 */
static bv64_abs_t tst[30];

int main(void) {
  uint32_t i;

  for (i=4; i<=64; i+=4) {
    make_interval_set(tst, i);
    run_tests(tst, 30);
  }

  return 0;
}
