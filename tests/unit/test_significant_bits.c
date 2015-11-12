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

#include "utils/bit_tricks.h"

/*
 * Number of significant bits in x
 * - if the result is k then -2^(k-1) <= x < 2^(k-1)
 */
static uint32_t num_significant_bits(int64_t x) {
  uint64_t mask;
  uint32_t k;

  mask = ((uint64_t) 1) << 63;
  k = 64;
  if (x < 0) {
    for (;;) {
      mask >>= 1;
      if ((mask & x) == 0) break;
      k --;
    }
  } else {
    for (;;) {
      mask >>= 1;
      if (mask == 0 || (mask & x) != 0) break;
      k --;
    }
  }

  return k;
}

/*
 * Variant implementations
 */
static uint32_t num_significant_bits_var(int64_t x) {
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

static uint32_t num_significant_bits_var2(int64_t x) {
  int64_t bound;
  uint32_t k;

  if (x < 0) {
    bound = INT64_MIN/2;
    k = 64;
    while (bound <= x) {
      bound /= 2;
      k --;
    }
  } else {
    bound = -(INT64_MIN/2);
    k = 64;
    while (x < bound) {
      bound /= 2;
      k --;
    }
  }
  return k;
}

static inline uint32_t num_leading_zeros(uint64_t x) {
  return (x == 0) ? 64 : clz64(x);
}

static uint32_t num_significant_bits_var3(int64_t x) {
  uint64_t y;

  y = (x < 0) ? ~((uint64_t) x) : ((uint64_t) x);
  return 65 - num_leading_zeros(y);
}


static void test_significant_bits(int64_t x, uint32_t expected_value) {
  uint32_t n;

  printf("\ntesting: %"PRId64"\n", x);
  n = num_significant_bits(x);
  printf("first method: %"PRIu32" significant bits\n", n);
  if (n != expected_value) goto error;

  n = num_significant_bits_var(x);
  printf("variant method: %"PRIu32" significant bits\n", n);
  if (n != expected_value) goto error;

  n = num_significant_bits_var2(x);
  printf("third method: %"PRIu32" significant bits\n", n);
  if (n != expected_value)  goto error;

  n = num_significant_bits_var3(x);
  printf("fourth method: %"PRIu32" significant bits\n", n);
  if (n != expected_value)  goto error;

  return;
  
 error:
  printf("*** BUG DETECTED: expected value = %"PRIu32" ***\n", expected_value);
  fflush(stdout);
  exit(1);
}

int main(void) {
  test_significant_bits(0, 1);
  test_significant_bits(-1, 1);
  test_significant_bits(-2, 2);
  test_significant_bits(-3, 3);
  test_significant_bits(-4, 3);
  test_significant_bits(-5, 4);
  test_significant_bits(-6, 4);
  test_significant_bits(1, 2);
  test_significant_bits(2, 3);
  test_significant_bits(3, 3);
  test_significant_bits(4, 4);
  test_significant_bits(5, 4);
  test_significant_bits(6, 4);

  test_significant_bits(INT64_MIN, 64);
  test_significant_bits(INT64_MAX, 64);
  test_significant_bits(INT64_MIN/2, 63);
  test_significant_bits(-(INT64_MIN/2), 64); 
  test_significant_bits(0x55555555, 32);
  test_significant_bits(-0x55555555, 32);

  test_significant_bits(0x800000, 25);
  test_significant_bits(0x80000, 21);
  test_significant_bits(0x8000, 17);
  test_significant_bits(0x800, 13);
  test_significant_bits(0x80, 9);
  test_significant_bits(0x8, 5);

  test_significant_bits(-0x800000, 24);
  test_significant_bits(-0x80000, 20);
  test_significant_bits(-0x8000, 16);
  test_significant_bits(-0x800, 12);
  test_significant_bits(-0x80, 8);
  test_significant_bits(-0x8, 4);

  test_significant_bits(0x7FFFFF, 24);
  test_significant_bits(0x7FFFF, 20);
  test_significant_bits(0x7FFF, 16);
  test_significant_bits(0x7FF, 12);
  test_significant_bits(0x7F, 8);
  test_significant_bits(0x7, 4);

  return 0;
}
