/*
 * GCD of two unsigned integers
 */

#include <assert.h>
#include "gcd.h"


/*
 * gcd of two 32bit unsigned positive numbers.
 */
uint32_t gcd32(uint32_t a, uint32_t b) {
  uint32_t x;
  uint32_t k;

  assert(a>0 && b>0);

  k = 1;
  x = a | b;
  while ((x & 1) == 0) {
    k <<= 1;
    x >>= 1;
    a >>= 1;
    b >>= 1;
  }

  do {
    if ((a & 1) == 0) {
      a >>= 1;
    } else if ((b & 1) == 0) {
      b >>= 1;
    } else if (a >= b) {
      a = (a - b) >> 1;
    } else {
      b = (b - a) >> 1;
    }
  } while (a > 0);

  return b * k;
}

/*
 * gcd of two 64bit unsigned positive numbers
 */
uint64_t gcd64(uint64_t a, uint64_t b) {
  uint64_t x;
  uint64_t k;

  assert(a>0 && b>0);

  k = 1;
  x = a | b;
  while ((x & 1) == 0) {
    k <<= 1;
    x >>= 1;
    a >>= 1;
    b >>= 1;
  }

  do {
    if ((a & 1) == 0) {
      a >>= 1;
    } else if ((b & 1) == 0) {
      b >>= 1;
    } else if (a >= b) {
      a = (a - b) >> 1;
    } else {
      b = (b - a) >> 1;
    }
  } while (a > 0);

  return b * k;
}



