/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "terms/bv64_constants.h"
#include "terms/bv64_interval_abstraction.h"


#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif

// conventions for true/false (as in smt_core.h)
enum {
  true_bit = 0,
  false_bit = 1,
};

static uint32_t random_bit(void) {
  return (random() & 0xffff) > 0x7fff;
}

// n-bits constant
static uint64_t random_constant(uint32_t n) {
  uint64_t x, mask;
  uint32_t i;

  assert(1 <= n && n <= 64);

  x = 0;
  mask = 1;
  for (i=0; i<n; i++) {
    if (random_bit()) {
      x |= mask;
    }
    mask <<= 1;
  }

  return x;
}

#if 0
// array of n random bits
static void random_const_array(int32_t *a, uint32_t n) {
  uint32_t i;

  assert(1 <= n && n <= 64);

  for (i=0; i<n; i++) {
    a[i] = random_bit(); // 0 --> true_bit, 1 --> false_bit
    assert(0 <= a[i] && a[i] <= 1);
  }
}
#endif

// random array
static void random_array(int32_t *a, uint32_t n) {
  uint32_t i;

  assert(1 <= n && n <= 64);

  for (i=0; i<n; i++) {
    a[i] = random() & 0x3F;
  }
}

// convert constant to an array of n bits
static void array_from_constant(int32_t *a, uint32_t n, uint64_t c) {
  uint32_t i;

  assert(1 <= n && n <= 64);

  for (i=0; i<n; i++) {
    a[i] = tst_bit64(c, i) ? true_bit : false_bit;
    assert(0 <= a[i] && a[i] <= 1);
  }
}

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

static void show_interval(FILE *f, bv64_abs_t *a) {
  char aux[30];

  sign2string(aux, a->sign);
  fprintf(f, "[%"PRId64", %"PRId64"] (%"PRIu32" bits, sign = %s)\n",
	  a->low, a->high, a->nbits, aux);
}

static void show_literal(FILE *f, int32_t l) {
  assert(l >= 0);

  switch (l) {
  case true_bit:
    fprintf(f, "tt");
    break;

  case false_bit:
    fprintf(f, "ff");
    break;

  default:
    if ((l & 1) == 0) {
      fprintf(f, "p!%"PRId32, (l >> 1));
    } else {
      fprintf(f, "~p!%"PRId32, (l >> 1));
    }
    break;
  }
}

static void show_array(FILE *f, int32_t *a, uint32_t n) {
  assert(n > 0);

  fprintf(f, "[");
  for (;;) {
    n --;
    show_literal(f, a[n]);
    if (n == 0) break;
    fprintf(f, " ");
  }
  fprintf(f, "]");
}

/*
 * Tests for constant bitvectors
 */
static void test_zero(void) {
  bv64_abs_t tst;

  printf("\nTesting: abstraction of 0\n");

  printf("abs_zero: ");
  bv64_abs_zero(&tst);
  show_interval(stdout, &tst);

  printf("abs(0, 5): ");
  bv64_abs_constant(&tst, 0, 5);
  show_interval(stdout, &tst);

  printf("abs(0, 63): ");
  bv64_abs_constant(&tst, 0, 63);
  show_interval(stdout, &tst);

  printf("abs(0, 64): ");
  bv64_abs_constant(&tst, 0, 64);
  show_interval(stdout, &tst);
}


static void test_one(void) {
  bv64_abs_t tst;

  printf("\nTesting: abstraction of 1\n");

  printf("abs_one: ");
  bv64_abs_one(&tst);
  show_interval(stdout, &tst);

  printf("abs(1, 5): ");
  bv64_abs_constant(&tst, 1, 5);
  show_interval(stdout, &tst);

  printf("abs(1, 63): ");
  bv64_abs_constant(&tst, 1, 63);
  show_interval(stdout, &tst);

  printf("abs(1, 64): ");
  bv64_abs_constant(&tst, 1, 64);
  show_interval(stdout, &tst);
}


static void test_minus_one(void) {
  bv64_abs_t tst;

  printf("\nTesting: abstraction of -1\n");

  printf("abs_minus_one: ");
  bv64_abs_minus_one(&tst);
  show_interval(stdout, &tst);

  printf("abs(-1, 5): ");
  bv64_abs_constant(&tst, mask64(5), 5);
  show_interval(stdout, &tst);

  printf("abs(-1, 63): ");
  bv64_abs_constant(&tst, mask64(63), 63);
  show_interval(stdout, &tst);

  printf("abs(-1, 64): ");
  bv64_abs_constant(&tst, mask64(64), 64);
  show_interval(stdout, &tst);
}

static void test_constant(uint64_t c, uint32_t n) {
  bv64_abs_t tst;

  assert(c == norm64(c, n));

  printf("Testing abstraction of %"PRIu64" (%"PRIu32" bits): ", c, n);
  bv64_abs_constant(&tst, c, n);
  show_interval(stdout, &tst);  
}

static void test_many_constants(uint32_t n) {
  uint64_t c;
  uint32_t i;

  printf("\nTesting %"PRIu32"-bit constants\n", n);
  if (n < 6) {
    // exhaustive test
    for (c=0; c < ((uint64_t) 1) << n; c++) {
      test_constant(c, n);
    }
  } else {
    for (i=0; i<50; i++) {
      c = random_constant(n);
      test_constant(c, n);
    }
  }
}


/*
 * Arrays of bits
 */
static void test_constant_array(uint32_t n, uint64_t c) {
  bv64_abs_t tst1, tst2;
  int32_t a[64];

  printf("Testing constant array with %"PRIu64" (%"PRIu32" bits)\n", c, n);
  printf("  abs constant gives: ");
  bv64_abs_constant(&tst1, c, n);
  show_interval(stdout, &tst1);
  
  printf("  abs array gives:    ");
  array_from_constant(a, n, c);
  bv64_abs_array(&tst2, false_bit, a, n);
  show_interval(stdout, &tst1);

  if (tst1.sign != tst2.sign || tst1.nbits != tst2.nbits || 
      tst1.low != tst2.low || tst1.high != tst2.high) {
    printf("*** BUG DETECTED: mistmatch ***\n");
    fflush(stdout);
    exit(1);
  }
}

static void test_constant_arrays(uint32_t n) {
  uint64_t c;
  uint32_t i;

  printf("\nTesting %"PRIu32"-bit constant arrays\n", n);

  if (n < 6) {
    for (c = 0; c < ((uint64_t) 1) << n; c++) {
      test_constant_array(n, c);
    }
  } else { 
    for (i=0; i<50; i++) {
      c = random_constant(n);
      test_constant_array(n, c);
    }
  }
}

static void test_random_arrays(uint32_t n) {
  bv64_abs_t tst;
  int32_t aux[64];
  uint32_t i;

  printf("\nTesting random %"PRIu32"-bit arrays\n", n);

  for (i=0; i<20; i++) {
    random_array(aux, n);
    printf("array: ");
    show_array(stdout, aux, n);
    printf("\n  abstraction: ");
    bv64_abs_array(&tst, false_bit, aux, n);
    show_interval(stdout, &tst);
  }

  printf("\n");
  random_array(aux, n);
  printf("array: ");
  show_array(stdout, aux, n);
  printf("\n  abstraction: ");
  bv64_abs_array(&tst, false_bit, aux, n);
  show_interval(stdout, &tst);

  // force low-order bits to zero
  i = n-1;
  while (i>0) {
    i --;
    aux[i] = false_bit;
    printf("array: ");
    show_array(stdout, aux, n);
    printf("\n  abstraction: ");
    bv64_abs_array(&tst, false_bit, aux, n);
    show_interval(stdout, &tst);
  }

  printf("\n");
  random_array(aux, n);
  printf("array: ");
  show_array(stdout, aux, n);
  printf("\n  abstraction: ");
  bv64_abs_array(&tst, false_bit, aux, n);
  show_interval(stdout, &tst);

  // force low-order bits to one
  i = n-1;
  while (i > 0) {
    i --;
    aux[i] = true_bit;
    printf("array: ");
    show_array(stdout, aux, n);
    printf("\n  abstraction: ");
    bv64_abs_array(&tst, false_bit, aux, n);
    show_interval(stdout, &tst);
  }
}




int main(void) {
  test_zero();
  test_one();
  test_minus_one();

  test_many_constants(1);
  test_many_constants(2);
  test_many_constants(3);
  test_many_constants(4);
  test_many_constants(5);

  test_many_constants(10);
  test_many_constants(20);
  test_many_constants(63);
  test_many_constants(64);

  test_constant_arrays(1);
  test_constant_arrays(2);
  test_constant_arrays(3);
  test_constant_arrays(4);

  test_constant_arrays(11);
  test_constant_arrays(16);
  test_constant_arrays(63);
  test_constant_arrays(64);

  test_random_arrays(1);
  test_random_arrays(2);
  test_random_arrays(3);
  test_random_arrays(4);

  test_random_arrays(11);
  test_random_arrays(16);
  test_random_arrays(63);
  test_random_arrays(64);


  return 0;
}
