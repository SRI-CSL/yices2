/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test conversion of bit-vector constants to mpz
 */

#include <stdlib.h>
#include <stdio.h>
#include <gmp.h>
#include <inttypes.h>
#include <assert.h>

#include "terms/bv_constants.h"

/*
 * Initialize z and copy a into z
 * - a is interpreted as an unsigned n-bit integer
 * - a must be normalized modulo (2^n)
 */
static inline void unsigned_bv2mpz(mpz_t z, uint32_t n, uint32_t *a) {
  uint32_t k;

  k = (n + 31) >> 5;
  mpz_init(z);
  bvconst_get_mpz(a, k, z);
}

/*
 * Initialize z and copy a into z
 * - a is interpreted as a signed n-bit integer
 * - a must be normalized modulo (2^n)
 */
static void signed_bv2mpz(mpz_t z, uint32_t n, uint32_t *a) {
  mpz_t aux;
  uint32_t k;

  assert(n > 0);

  k = (n + 31) >> 5;
  mpz_init(z);
  bvconst_get_mpz(a, k, z);
  if (bvconst_tst_bit(a, n-1)) { // sign bit = 1
    mpz_init_set_si(aux, -1);
    mpz_mul_2exp(aux, aux, n);
    mpz_add(z, z, aux);
    mpz_clear(aux);
  }
}


/*
 * Test convertions to mpz
 */
static void test_signed_conversion(uint32_t *a, uint32_t n) {
  mpz_t z;

  printf("Signed conversion: ");
  bvconst_print(stdout, a, n);
  signed_bv2mpz(z, n, a);
  printf(" = ");
  mpz_out_str(stdout, 10, z);
  printf("\n");
  mpz_clear(z);
}

static void test_signed_conversions(void) {
  uint32_t a[4];

  bvconst_clear(a, 2);
  test_signed_conversion(a, 1);
  test_signed_conversion(a, 2);
  test_signed_conversion(a, 30);
  test_signed_conversion(a, 31);
  test_signed_conversion(a, 32);
  test_signed_conversion(a, 33);
  test_signed_conversion(a, 64);

  bvconst_set_one(a, 2);
  test_signed_conversion(a, 1);
  test_signed_conversion(a, 2);
  test_signed_conversion(a, 30);
  test_signed_conversion(a, 31);
  test_signed_conversion(a, 32);
  test_signed_conversion(a, 33);
  test_signed_conversion(a, 64);

  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 2);
  test_signed_conversion(a, 2);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 30);
  test_signed_conversion(a, 30);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 31);
  test_signed_conversion(a, 31);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 32);
  test_signed_conversion(a, 32);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 33);
  test_signed_conversion(a, 33);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 64);
  test_signed_conversion(a, 64);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 1);
  bvconst_normalize(a, 2);
  test_signed_conversion(a, 2);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 29);
  bvconst_normalize(a, 30);
  test_signed_conversion(a, 30);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 30);
  bvconst_normalize(a, 31);
  test_signed_conversion(a, 31);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 31);
  bvconst_normalize(a, 32);
  test_signed_conversion(a, 32);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 32);
  bvconst_normalize(a, 33);
  test_signed_conversion(a, 33);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 63);
  bvconst_normalize(a, 64);
  test_signed_conversion(a, 64);
}

/*
 * Test convertions to mpz
 */
static void test_unsigned_conversion(uint32_t *a, uint32_t n) {
  mpz_t z;

  printf("Unsigned conversion: ");
  bvconst_print(stdout, a, n);
  unsigned_bv2mpz(z, n, a);
  printf(" = ");
  mpz_out_str(stdout, 10, z);
  printf("\n");
  mpz_clear(z);
}

static void test_unsigned_conversions(void) {
  uint32_t a[4];

  bvconst_clear(a, 2);
  test_unsigned_conversion(a, 1);
  test_unsigned_conversion(a, 2);
  test_unsigned_conversion(a, 30);
  test_unsigned_conversion(a, 31);
  test_unsigned_conversion(a, 32);
  test_unsigned_conversion(a, 33);
  test_unsigned_conversion(a, 64);

  bvconst_set_one(a, 2);
  test_unsigned_conversion(a, 1);
  test_unsigned_conversion(a, 2);
  test_unsigned_conversion(a, 30);
  test_unsigned_conversion(a, 31);
  test_unsigned_conversion(a, 32);
  test_unsigned_conversion(a, 33);
  test_unsigned_conversion(a, 64);

  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 2);
  test_unsigned_conversion(a, 2);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 30);
  test_unsigned_conversion(a, 30);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 31);
  test_unsigned_conversion(a, 31);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 32);
  test_unsigned_conversion(a, 32);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 33);
  test_unsigned_conversion(a, 33);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 64);
  test_unsigned_conversion(a, 64);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 1);
  bvconst_normalize(a, 2);
  test_unsigned_conversion(a, 2);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 29);
  bvconst_normalize(a, 30);
  test_unsigned_conversion(a, 30);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 30);
  bvconst_normalize(a, 31);
  test_unsigned_conversion(a, 31);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 31);
  bvconst_normalize(a, 32);
  test_unsigned_conversion(a, 32);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 32);
  bvconst_normalize(a, 33);
  test_unsigned_conversion(a, 33);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 63);
  bvconst_normalize(a, 64);
  test_unsigned_conversion(a, 64);
}


int main(void) {
  test_signed_conversions();
  test_unsigned_conversions();
  return 0;
}
