/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST CONSTRUCTORS OF BIT-VECTOR CONSTANTS
 */
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>

#include <gmp.h>

#include "yices.h"


/*
 * Check that term is equal to the bit-vector constant stored in a.
 * - n = size of a = number of bits
 *
 * This relies on the fact that Yices normalizes constants and 
 * uses hash-consing.
 */
static void check_bvconst(term_t t, uint32_t n, const int32_t a[]) {
  term_t u;

  u = yices_bvconst_from_array(n, a);
  if (u != t) {
    printf("FAILED\n");
    printf("got value:  ");
    yices_pp_term(stdout, t, 200, 1, 0);   
    printf("expected value: ");
    yices_pp_term(stdout, u, 200, 1, 0);
    fflush(stdout);
    exit(1);
  }
}



/*
 * Store value x into array a
 * - n = size of array a (must be at least as large as the size of x)
 * - use zero extend or sign extend
 */
static void zero_extend_uint32(uint32_t x, uint32_t n, int32_t a[]) {
  uint32_t i, mask;

  assert(n >= 32);

  mask = 1;
  for (i=0; i<32; i++) {
    a[i] = ((x & mask) == 0) ? 0 : 1;
    mask <<= 1;
  }

  while (i < n) {
    a[i] = 0;
    i ++;
  }
}

static void zero_extend_uint64(uint64_t x, uint32_t n, int32_t a[]) {
  uint32_t i;
  uint64_t mask;

  assert(n >= 64);

  mask = 1;
  for (i=0; i<64; i++) {
    a[i] = ((x & mask) == 0) ? 0 : 1;
    mask <<= 1;
  }
  while (i < n) {
    a[i] = 0;
    i ++;
  }
}

static void sign_extend_int32(int32_t x, uint32_t n, int32_t a[]) {
  uint32_t i, lx, mask;
  int32_t sign;

  assert(n >= 32);

  lx = (uint32_t) (x & 0x7FFFFFFF);
  sign = (x < 0);
  mask = 1;
  for (i=0; i<31; i++) {
    a[i] = ((lx & mask) == 0) ? 0 : 1;
    mask <<= 1;
  }
  while (i < n) {
    a[i] = sign;
    i ++;
  }
}

static void sign_extend_int64(int64_t x, uint32_t n, int32_t a[]) {
  uint64_t lx, mask;
  uint32_t i;
  int32_t sign;

  assert(n >= 64);

  lx = (uint64_t) (x & 0x7FFFFFFFFFFFFFFF);
  sign = (x < 0);
  mask = 1;
  for (i=0; i<63; i++) {
    a[i] = ((lx & mask) == 0) ? 0 : 1;
    mask <<= 1;
  }

  while (i < n) {
    a[i] = sign;
    i ++;
  }
}


/*
 * Copy an mpz number
 */
static void sign_extend_mpz(mpz_t z, uint32_t n, int32_t a[]) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i] = mpz_tstbit(z, i);
  }
}



/*
 * Test 
 */
#define MAXBITS 120

static void test_bvconst_uint32(uint32_t x) {
  int32_t a[MAXBITS];
  uint32_t n;
  term_t t;

  printf("Testing yices_bvconst_uint32: x = %"PRIu32"\n", x);
  zero_extend_uint32(x, MAXBITS, a); 
  for (n=1; n<MAXBITS; n++) {
    t = yices_bvconst_uint32(n, x);
    printf("--> %3"PRIu32" bits: ", n);
    yices_pp_term(stdout, t, 200, 1, 0);
    check_bvconst(t, n, a);
  }
  printf("passed\n\n");
}

static void test_bvconst_int32(int32_t x) {
  int32_t a[MAXBITS];
  uint32_t n;
  term_t t;

  printf("Testing yices_bvconst_int32: x = %"PRId32"\n", x);
  sign_extend_int32(x, MAXBITS, a); 
  for (n=1; n<MAXBITS; n++) {
    t = yices_bvconst_int32(n, x);
    printf("--> %3"PRIu32" bits: ", n);
    yices_pp_term(stdout, t, 200, 1, 0);
    check_bvconst(t, n, a);
  }
  printf("passed\n\n");
}

static void test_bvconst_uint64(uint64_t x) {
  int32_t a[MAXBITS];
  uint32_t n;
  term_t t;

  printf("Testing yices_bvconst_uint64: x = %"PRIu64"\n", x);
  zero_extend_uint64(x, MAXBITS, a); 
  for (n=1; n<MAXBITS; n++) {
    t = yices_bvconst_uint64(n, x);
    printf("--> %3"PRIu32" bits: ", n);
    yices_pp_term(stdout, t, 200, 1, 0);
    check_bvconst(t, n, a);
  }
  printf("passed\n\n");
}

static void test_bvconst_int64(int64_t x) {
  int32_t a[MAXBITS];
  uint32_t n;
  term_t t;

  printf("Testing yices_bvconst_int64: x = %"PRId64"\n", x);
  sign_extend_int64(x, MAXBITS, a); 
  for (n=1; n<MAXBITS; n++) {
    t = yices_bvconst_int64(n, x);
    printf("--> %3"PRIu32" bits: ", n);
    yices_pp_term(stdout, t, 200, 1, 0);
    check_bvconst(t, n, a);
  }
  printf("passed\n\n");
}



/*
 * Tests using a GMP integer:
 * - the input is given as a string
 */
static void test_bvconst_mpz(const char *s) {
  int32_t a[MAXBITS];
  mpz_t z;
  uint32_t n;
  term_t t;

  printf("Testing yices_bvconst_mpz: x = %s\n", s);
  mpz_init(z);
  mpz_set_str(z, s, 0);
  sign_extend_mpz(z, MAXBITS, a);
  for (n=1; n<MAXBITS; n++) {
    t = yices_bvconst_mpz(n, z);
    printf("--> %3"PRIu32" bits: ", n);
    yices_pp_term(stdout, t, 200, 1, 0);
    check_bvconst(t, n, a);
  }
  mpz_clear(z);
  printf("passed\n\n");
}


int main(void) {
  yices_init();

  test_bvconst_uint32(0);
  test_bvconst_uint32(1);
  test_bvconst_uint32(UINT32_MAX);
  test_bvconst_uint32(0xAAAAAAAAu);
  test_bvconst_uint32(0x55555555u);

  test_bvconst_uint64(0);
  test_bvconst_uint64(1);
  test_bvconst_uint64(UINT64_MAX);
  test_bvconst_uint64(0xAAAAAAAAAAAAAAAAu);
  test_bvconst_uint64(0x5555555555555555u);

  test_bvconst_int32(0);
  test_bvconst_int32(1);
  test_bvconst_int32(-1);
  test_bvconst_int32(INT32_MAX);
  test_bvconst_int32(INT32_MIN);
  test_bvconst_int32(0xAAAAAAAA);
  test_bvconst_int32(0x55555555);

  test_bvconst_int64(0);
  test_bvconst_int64(1);
  test_bvconst_int64(-1);
  test_bvconst_int64(INT64_MAX);
  test_bvconst_int64(INT64_MIN);
  test_bvconst_int64(0xAAAAAAAAAAAAAAAA);
  test_bvconst_int64(0x5555555555555555);

  test_bvconst_mpz("0");
  test_bvconst_mpz("1");
  test_bvconst_mpz("-1");
  test_bvconst_mpz("0b10101010101010101010101010");
  test_bvconst_mpz("-0b10101010101010101010101010");
  test_bvconst_mpz("123456789012345678901234567890");
  test_bvconst_mpz("-123456789012345678901234567890");
  yices_exit();

  printf("All tests succeeded\n");
  
  return 0;
}
