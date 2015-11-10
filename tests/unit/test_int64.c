/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include <gmp.h>


/*
 * EXACT ARITHMETIC USING GMP NUMBERS
 */

/*
 * Store x into z. z must be initialized
 * We split x into two 32bit integers to make sure this works
 * even if (signed long int) is 32bits.
 */
static void mpz_set_int64(mpz_t z, int64_t x) {
  mpz_set_si(z, (x >> 32));
  mpz_mul_2exp(z, z, 32);
  mpz_add_ui(z, z, (uint32_t) x);

  //  printf("mpz_set: x = %"PRId64", z = ", x);
  //  mpz_out_str(stdout, 10, z);
  //  printf("\n");
}

static void mpz_add_int64(mpz_t z, int64_t x) {
  mpz_t aux;

  mpz_init(aux);
  mpz_set_int64(aux, x);
  mpz_add(z, z, aux);
  mpz_clear(aux);
}

static void mpz_sub_int64(mpz_t z, int64_t x) {
  mpz_t aux;

  mpz_init(aux);
  mpz_set_int64(aux, x);
  mpz_sub(z, z, aux);
  mpz_clear(aux);
}

static void mpz_mul_int64(mpz_t z, int64_t x) {
  mpz_t aux;

  mpz_init(aux);
  mpz_set_int64(aux, x);
  mpz_mul(z, z, aux);
  mpz_clear(aux);
}


/*
 * Store -2^k-1 into z
 */
static void mpz_set_min_int(mpz_t z, uint32_t k) {
  assert(k >= 1);
  mpz_set_si(z, -1);
  mpz_mul_2exp(z, z, k-1);
}

/*
 * Store 2^k-1 into z
 */
static void mpz_set_max_int(mpz_t z, uint32_t k) {
  assert(k >= 1);
  mpz_set_si(z, 1);
  mpz_mul_2exp(z, z, k-1);
  mpz_sub_ui(z, z, 1);
}

/*
 * Check whether z == x
 */
static bool mpz_eq_int64(mpz_t z, int64_t x) {
  mpz_t aux;
  bool eq;

  mpz_init(aux);
  mpz_set_int64(aux, x);
  eq = (mpz_cmp(z, aux) == 0);
  mpz_clear(aux);

  return eq;
}

/*
 * Check whether -2^k <= z <= 2^k - 1
 */
static bool mpz_fits(mpz_t z, uint32_t k) {
  mpz_t min, max;
  bool fits;

  mpz_init(min);
  mpz_init(max);
  mpz_set_min_int(min, k);
  mpz_set_max_int(max, k);
  fits = mpz_cmp(min, z) <= 0 && mpz_cmp(z, max) <= 0;
  mpz_clear(min);
  mpz_clear(max);

  return fits;
}



/*
 * ARITHMETIC ON SIGNED K-BIT CONSTANTS
 */

/*
 * These functions are copied from bv64_interval_abstraction.c
 */
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

// check whether x has k significant bits
static inline bool fits_k_bits(int64_t x, uint32_t k) {
  return min_int(k) <= x && x <= max_int(k);
}

// opposite of x: set overflow to true if the result requires k+1 bits
static inline int64_t opposite(int64_t x, uint32_t k, bool *overflow) {
  assert(fits_k_bits(x, k));
  *overflow = (x == min_int(k));
  return -x;
}

// sum: x + y
static int64_t sum(int64_t x, int64_t y, uint32_t k, bool *overflow) {
  int64_t s;

  assert(fits_k_bits(x, k) && fits_k_bits(y, k));

  s = x + y;
  if (k < 64) {
    *overflow = !fits_k_bits(s, k);
  } else {
    *overflow = (x < 0 &&  y < 0 && s >= 0) || (x >= 0 && y >= 0 && s < 0);
  }
  return s;
}

// diff: x - y
static int64_t diff(int64_t x, int64_t y, uint32_t k, bool *overflow) {
  int64_t d;

  assert(fits_k_bits(x, k) && fits_k_bits(y, k));
  d = x - y;
  if (k < 64) {
    *overflow = !fits_k_bits(d, k);
  } else {
    *overflow = (x < 0 && y >= 0 && d >= 0) || (x >= 0 && y < 0 && d < 0);
  }

  return d;
}


/*
 * Auxiliary function:
 * - a is an array of 4 unsigned 32bit integers
 *   that represents a[0] + 2^32 a[1] + 2^64 a[2] + 2^96 a[3]
 * - this function adds the product x * y * 2^(32 * i) to a
 */
static void add_mul(uint32_t a[4], uint32_t x, uint32_t y, uint32_t i) {
  uint64_t p;

  assert(i <= 2);
  p = ((uint64_t) x) * y;
  while (i < 4) {
    p += a[i];
    a[i] = (uint32_t) (p & 0xFFFFFFFF);
    p >>= 32;
    i ++;
  }
}

#ifndef NDEBUG
// same as mpz_set_int64 for unsigned int
static void mpz_set_uint64(mpz_t z, uint64_t x) {
  mpz_set_ui(z, (x >> 32));
  mpz_mul_2exp(z, z, 32);
  mpz_add_ui(z, z, (uint32_t) x);
}

static void mpz_mul_uint64(mpz_t z, uint64_t x) {
  mpz_t aux;

  mpz_init(aux);
  mpz_set_uint64(aux, x);
  mpz_mul(z, z, aux);
  mpz_clear(aux);
}

// store a[0] + 2^32 a[1] + 2^64 a[2] + 2^96 a[3] into z
static void mpz_set_uint128(mpz_t z, uint32_t a[4]) {
  mpz_set_ui(z, a[3]);
  mpz_mul_2exp(z, z, 32);
  mpz_add_ui(z, z, a[2]);
  mpz_mul_2exp(z, z, 32);
  mpz_add_ui(z, z, a[1]);
  mpz_mul_2exp(z, z, 32);
  mpz_add_ui(z, z, a[0]);
}

/*
 * Check the result of mul:
 * - a is expected to contain the result of x * y
 */
static bool good_mul(uint32_t a[4], uint64_t x, uint64_t y) {
  mpz_t p, q;
  bool eq;

  mpz_init(p);
  mpz_init(q);

  mpz_set_uint64(p, x);
  mpz_mul_uint64(p, y);

  mpz_set_uint128(q, a);
  eq = (mpz_cmp(p, q) == 0);

  mpz_clear(q);
  mpz_clear(p);

  return eq;
}
#endif

/*
 * Product x.y
 * - both are arbitrary int64_t
 * - overflow is set if the result has more than 64bits
 */
static int64_t mul(int64_t x, int64_t y, bool *overflow) {
  uint32_t result[4];
  uint64_t abs_x, abs_y, c, d;
  uint32_t x0, x1, y0, y1;

  abs_x = (x < 0) ? (uint64_t) (- x) : x;
  abs_y = (y < 0) ? (uint64_t) (- y) : y;

  x0 = abs_x & 0xFFFFFFFF;
  x1 = abs_x >> 32;
  y0 = abs_y & 0xFFFFFFFF;
  y1 = abs_y >> 32;

  result[0] = 0;
  result[1] = 0;
  result[2] = 0;
  result[3] = 0;

  add_mul(result, x0, y0, 0);
  add_mul(result, x0, y1, 1);
  add_mul(result, x1, y0, 1);
  add_mul(result, x1, y1, 2);

  assert(good_mul(result, abs_x, abs_y));

  c = result[0] + (((uint64_t) result[1]) << 32);
  d = result[2] + (((uint64_t) result[3]) << 32);

  if ((x < 0 && y < 0) || (x >= 0 && y >= 0)) {
    *overflow = (d != 0) || (c > (uint64_t) INT64_MAX);
    return c;
  } else {
    // we use the fact that -INT64_MIN == INT64_MIN
    // (assuming 2s complement arithmetic)
    *overflow = (d != 0) || (c > (uint64_t) INT64_MIN);
    return - (int64_t) c;
  }
}



/*
 * x^d
 */
static int64_t power(int64_t x, uint32_t d, bool *overflow) {
  int64_t y;

  y = 1;
  *overflow = false;

  while (d != 0) {
    if ((d & 1) != 0) {
      y = mul(y, x, overflow); // y := y * x
      if (*overflow) break;
    }
    d >>= 1;
    if (d > 0) {
      x = mul(x, x, overflow); // x := x * x 
      if (*overflow) break;
    }
  }

  return y;
}


/*
 * TESTS
 */

/*
 * Check whether z == x. If not report a bug
 */
static void mpz_check_eq(mpz_t z, int64_t x) {
  if (! mpz_eq_int64(z, x)) {
    printf("*** BUG check_eq failed ***\n");
    fflush(stdout);
    exit(1);
  }
}

/*
 * Check whether z fits on k bits
 */
static void mpz_check_fit(mpz_t z, uint32_t k) {
  if (! mpz_fits(z, k)) {
    printf("*** BUG: check_fit failed ***\n");
    fflush(stdout);
    exit(1);
  }
}

static void mpz_check_overflow(mpz_t z, uint32_t k) {
  if (mpz_fits(z, k)) {
    printf("*** BUG: check_overflow failed ***\n");
    fflush(stdout);
    exit(1);
  }
}


/*
 * Test of min_int and max_int
 */
static void test_min_max(void) {
  mpz_t tst;
  int64_t x;
  uint32_t i;  

  mpz_init(tst);

  for (i=1; i<=64; i++) {
    x = min_int(i);
    printf("min_int(%"PRIu32") = %"PRId64"\n", i, x);
    mpz_set_min_int(tst, i);
    mpz_check_eq(tst, x);
  }
  printf("\n");
  for (i=1; i<=64; i++) {
    x = max_int(i);
    printf("max_int(%"PRIu32") = %"PRId64"\n", i, x);
    mpz_set_max_int(tst, i);
    mpz_check_eq(tst, x);
  }
  printf("\n");

  mpz_clear(tst);
}


/*
 * Test opposite: n = number of bits
 */
static void test_opp(int64_t x, uint32_t n) {
  mpz_t tst;
  int64_t y;
  bool overflow;
  
  assert(fits_k_bits(x, n));

  mpz_init(tst);

  y = opposite(x, n, &overflow);
  printf("opp(%"PRId64") = %"PRId64, x, y);

  if (overflow) {
    printf(" ---> overflow\n");
    if (n<64 && !fits_k_bits(y, n+1)) {
      printf("*** BUG ***\n");
      exit(1);
    }
  } else {
    printf("\n");
    if (!fits_k_bits(y, n)) {
      printf("*** BUG ***\n");
      exit(1);
    }
  }

  mpz_set_int64(tst, x);
  mpz_neg(tst, tst);
  if (n<64) {
    mpz_check_eq(tst, y);
  }
  if (overflow) {
    mpz_check_overflow(tst, n);
    mpz_check_fit(tst, n + 1);
  } else {
    mpz_check_fit(tst, n);
  }

  mpz_clear(tst);
}

/*
 * add/sub
 */
static void test_add(int64_t x, int64_t y, uint32_t n) {
  mpz_t tst;
  int64_t z;
  bool overflow;

  assert(fits_k_bits(x, n) && fits_k_bits(y, n));

  mpz_init(tst);

  z = sum(x, y, n, &overflow);
  printf("sum(%"PRId64", %"PRId64") = %"PRId64, x, y, z);
  if (overflow) {
    printf(" ---> overflow\n");
    if (n<64 && !fits_k_bits(z, n+1)) {
      printf("*** BUG ***\n");
      exit(1);
    }
  } else {
    printf("\n");
    if (!fits_k_bits(z, n)) {
      printf("*** BUG ***\n");
      exit(1);
    }
  }

  mpz_set_int64(tst, x);
  mpz_add_int64(tst, y);
  if (n < 64) {
    mpz_check_eq(tst, z);
  }
  if (overflow) {
    mpz_check_overflow(tst, n);
    mpz_check_fit(tst, n+1);
  } else {
    mpz_check_fit(tst, n);
  }

  mpz_clear(tst);
}

static void test_sub(int64_t x, int64_t y, uint32_t n) {
  mpz_t tst;
  int64_t z;
  bool overflow;

  assert(fits_k_bits(x, n) && fits_k_bits(y, n));

  mpz_init(tst);

  z = diff(x, y, n, &overflow);
  printf("diff(%"PRId64", %"PRId64") = %"PRId64, x, y, z);
  if (overflow) {
    printf(" ---> overflow\n");
    if (n<64 && !fits_k_bits(z, n+1)) {
      printf("*** BUG ***\n");
      exit(1);
    }
  } else {
    printf("\n");
    if (!fits_k_bits(z, n)) {
      printf("*** BUG ***\n");
      exit(1);
    }
  }

  mpz_set_int64(tst, x);
  mpz_sub_int64(tst, y);
  if (n < 64) {
    mpz_check_eq(tst, z);
  }
  if (overflow) {
    mpz_check_overflow(tst, n);
    mpz_check_fit(tst, n+1);
  } else {
    mpz_check_fit(tst, n);
  }

  mpz_clear(tst);
}

/*
 * product x * y
 */
static void test_mul(int64_t x, int64_t y, uint32_t n) {
  mpz_t tst;
  int64_t z;
  bool overflow;

  assert(fits_k_bits(x, n) && fits_k_bits(y, n));

  mpz_init(tst);

  z = mul(x, y, &overflow);
  printf("mul(%"PRId64", %"PRId64") = %"PRId64, x, y, z);
  if (overflow) {
    printf(" ---> overflow\n");
  } else {
    printf("\n");
  }

  mpz_set_int64(tst, x);
  mpz_mul_int64(tst, y);
  if (overflow) {
    mpz_check_overflow(tst, 64);
  } else {
    mpz_check_fit(tst, 64);
    mpz_check_eq(tst, z);
  }

  mpz_clear(tst);
}


/*
 * Power: x^d
 */
static void test_power(int64_t x, uint32_t n, uint32_t d) {
  mpz_t tst;
  int64_t z;
  bool overflow;

  assert(fits_k_bits(x, n));

  mpz_init(tst);

  z = power(x, d, &overflow);
  printf("power(%"PRId64", %"PRId32") = %"PRId64, x, d, z);
  if (overflow) {
    printf(" ---> overflow\n");
  } else {
    printf("\n");
  }

  mpz_set_int64(tst, x);
  mpz_pow_ui(tst, tst, d);
  if (overflow) {
    mpz_check_overflow(tst, 64);
  } else {
    mpz_check_fit(tst, 64);
    mpz_check_eq(tst, z);
  }

  mpz_clear(tst);
}



/*
 * Test operations: n = number of bits
 */
static void test_opposite(uint32_t n) {
  int64_t min, max;
  int64_t x;

  printf("\nTesting opposite: %"PRIu32" bits\n", n);
  min = min_int(n);
  max = max_int(n);
  printf("min = %"PRId64", max = %"PRId64"\n", min, max);

  if (n <= 6) {
    for (x=min; x<= max; x++) {
      test_opp(x, n);
    }
  } else {
    test_opp(min, n);
    test_opp(min+1, n);
    test_opp(min+2, n);
    test_opp(min/2, n);
    test_opp(-(max/2), n);
    test_opp(-2, n);
    test_opp(-1, n);
    test_opp(0, n);
    test_opp(1, n);
    test_opp(2, n);
    test_opp(max/2, n);
    test_opp(-(min/2), n);
    test_opp(max-2, n);
    test_opp(max-1, n);
    test_opp(max, n);
  }
}



static void test_add_sub(int64_t x, int64_t y, uint32_t n) {
  test_add(x, y, n);
  test_sub(x, y, n);
  test_sub(y, x, n);
}

static void sample_add_sub(int64_t x, uint32_t n) {
  int64_t min, max;

  min = min_int(n);
  max = max_int(n);

  test_add_sub(x, min, n);
  test_add_sub(x, min+1, n);
  test_add_sub(x, min+2, n);
  test_add_sub(x, min/4, n);
  test_add_sub(x, -(max/4), n);
  test_add_sub(x, -2, n);
  test_add_sub(x, -1, n);
  test_add_sub(x, 0, n);
  test_add_sub(x, 1, n);
  test_add_sub(x, 2, n);
  test_add_sub(x, max/4, n);
  test_add_sub(x, -(max/4), n);
  test_add_sub(x, max-2, n);
  test_add_sub(x, max-1, n);
  test_add_sub(x, max, n);
}

static void test_add_subs(uint32_t n) {
  int64_t min, max;
  int64_t x,  y;

  printf("\nTesting add and sub: %"PRIu32" bits\n", n);
  min = min_int(n);
  max = max_int(n);
  printf("min = %"PRId64", max = %"PRId64"\n", min, max);

  if (n <= 4) {
    for (x=min; x<=max; x++) {
      for (y=min; y<=max; y++) {
	test_add_sub(x, y, n);
      }
    }
  } else if (n <= 6) {
    for (x=min; x<=max; x++) {
      sample_add_sub(x, n);
    }
  } else {
    sample_add_sub(min, n);
    sample_add_sub(min+1, n);
    sample_add_sub(min+2, n);
    sample_add_sub(-2, n);
    sample_add_sub(-1, n);
    sample_add_sub(0, n);
    sample_add_sub(1, n);
    sample_add_sub(2, n);
    sample_add_sub(max-2, n);
    sample_add_sub(max-1, n);
    sample_add_sub(max, n);
  }
}

static void sample_mul(int64_t x, uint32_t n) {
  int64_t min, max;

  min = min_int(n);
  max = max_int(n);

  test_mul(x, min, n);
  test_mul(x, min+1, n);
  test_mul(x, min+2, n);
  test_mul(x, min/2, n);
  test_mul(x, min/3, n);
  test_mul(x, min/4, n);
  test_mul(x, -2, n);
  test_mul(x, -1, n);
  test_mul(x, 0, n);
  test_mul(x, 1, n);
  test_mul(x, 2, n);
  test_mul(x, max/4, n);
  test_mul(x, max/3, n);
  test_mul(x, max/2, n);
  test_mul(x, max-2, n);
  test_mul(x, max-1, n);
  test_mul(x, max, n);  
}

static void test_product(uint32_t n) {
  int64_t min, max;
  int64_t x,  y;

  printf("\nTesting mul: %"PRIu32" bits\n", n);
  min = min_int(n);
  max = max_int(n);

  if (n <= 4) {
    for (x=min; x<=max; x++) {
      for (y=min; y<=max; y++) {
	test_mul(x, y, n);
      }
    }
  } else if (n <= 6) {
    for (x=min; x<=max; x++) {
      sample_mul(x, n);
    }
  } else {
    sample_mul(min, n);
    sample_mul(min+1, n);
    sample_mul(min+2, n);
    sample_mul(min/2, n);
    sample_mul(min/3, n);
    sample_mul(min/4, n);
    sample_mul(-2, n);
    sample_mul(-1, n);
    sample_mul(0, n);
    sample_mul(1, n);
    sample_mul(2, n);
    sample_mul(max/4, n);
    sample_mul(max/3, n);
    sample_mul(max/2, n);
    sample_mul(max-2, n);
    sample_mul(max-1, n);
    sample_mul(max, n);
  }
}

static void test_powers_of_x(int64_t x, uint32_t n) {
  uint32_t d;

  for (d=0; d<8; d++) {
    test_power(x, n, d);
  }  
}


static void test_powers(uint32_t n) {
  int64_t min, max;
  int64_t x;

  printf("\nTesting powers: %"PRIu32" bits\n\n", n);

  min = min_int(n);
  max = max_int(n);
    if (n <= 6) {
    for (x=min; x<= max; x++) {
      test_powers_of_x(x, n);
    }
  } else {
    test_powers_of_x(min, n);
    test_powers_of_x(min+1, n);
    test_powers_of_x(min+2, n);
    test_powers_of_x(min/2, n);
    test_powers_of_x(-(max/2), n);
    test_powers_of_x(-2, n);
    test_powers_of_x(-1, n);
    test_powers_of_x(0, n);
    test_powers_of_x(1, n);
    test_powers_of_x(2, n);
    test_powers_of_x(max/2, n);
    test_powers_of_x(-(min/2), n);
    test_powers_of_x(max-2, n);
    test_powers_of_x(max-1, n);
    test_powers_of_x(max, n);
  }
}

int main(void) {
  uint32_t n;

  test_min_max();

  for (n=1; n<=6; n++) {
    test_opposite(n);
  }
  test_opposite(10);
  test_opposite(31);
  test_opposite(32);
  test_opposite(33);
  test_opposite(63);
  test_opposite(64);

  for (n=1; n<=6; n++) {
    test_add_subs(n);
  }
  test_add_subs(10);
  test_add_subs(31);
  test_add_subs(32);
  test_add_subs(33);
  test_add_subs(63);
  test_add_subs(64);

  for (n=1; n<=6; n++) {
    test_product(n);
  }
  test_product(10);
  test_product(31);
  test_product(32);
  test_product(33);
  test_product(63);
  test_product(64);

  for (n=1; n<=6; n++) {
    test_powers(n);
  }
  test_powers(10);
  test_powers(31);
  test_powers(32);
  test_powers(33);
  test_powers(63);
  test_powers(64);

  return 0;
}
