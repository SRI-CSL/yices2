/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * OPERATIONS ON SMALL BITVECTOR CONSTANTS
 */

#include <ctype.h>

#include "terms/bv64_constants.h"
#include "terms/bv_constants.h"


/*
 * Convert c into a signed 64 bit number
 */
int64_t signed_int64(uint64_t c, uint32_t n) {
  assert(0 < n && n <= 64);
  if (is_neg64(c, n)) {
    return c | ~mask64(n); // sign extend
  } else {
    return c;
  }
}


/*
 * Check whether a >= b: both are interpreted as n-bit signed numbers
 */
bool signed64_ge(uint64_t a, uint64_t b, uint32_t n) {
  uint64_t sa, sb;

  sa = a & sgn_bit_mask64(n); // sign of a << (n-1)
  sb = b & sgn_bit_mask64(n); // sign of b << (n-1)

  // a >= b iff (sign of a = 0 and sign of b = 1)
  //         or (sign_of a == sign_of b and a >= b);
  return (sa < sb) || (sa == sb && a >= b);
}

/*
 * Check whether a>b: both are interpreted as n-bit signed numbers
 */
bool signed64_gt(uint64_t a, uint64_t b, uint32_t n) {
  uint64_t sa, sb;

  sa = a & sgn_bit_mask64(n); // sign of a << (n-1)
  sb = b & sgn_bit_mask64(n); // sign of b << (n-1)

  // a >= b iff (sign of a = 0 and sign of b = 1)
  //         or (sign_of a == sign_of b and a > b);
  return (sa < sb) || (sa == sb && a > b);
}




/*
 * Shift left: (a << b), padding with 0.
 * - n = number of bits in a and b
 * - if b is more than n, this returns 0b00000
 * - the result is normalized
 */
uint64_t bvconst64_lshl(uint64_t a, uint64_t b, uint32_t n) {
  uint64_t c;

  assert(0 < n && n <= 64);

  c = 0;
  if (b < n) {
    assert(b < 64);
    c = norm64(a << b, n);
  }

  return c;
}


/*
 * Logical shift right: (a >> b), padding with 0
 * - n = number of bits in a and b
 * - if b is more than n, return 0b00000
 * - the result is normalized.
 */
uint64_t bvconst64_lshr(uint64_t a, uint64_t b, uint32_t n) {
  uint64_t c;

  assert(0 < n && n <= 64);

  c = 0;
  if (b < n) {
    assert(b < 64);
    c = norm64(a >> b, n);
  }

  return c;
}


/*
 * Arithmetic shift right: (a >> b), padding with a's sign bit
 * - n = number of bits in a and b
 * - if b is more than n, return 0b00000 or 0b11111 depending on a's sign bit
 * - the result is normalized.
 */
uint64_t bvconst64_ashr(uint64_t a, uint64_t b, uint32_t n) {
  int64_t c;

  assert(0 < n && n <= 64);

  c = signed_int64(a, n);
  if (b < n) {
    assert(0 <= b && b < 64);
    c = (int64_t) norm64((uint64_t) (c >> (int64_t) b), n);
  } else if (c < 0) {
    c = (int64_t) -1;
    c = (int64_t) norm64(c, n);
  } else {
    c = 0;
  }

  return (uint64_t) c;
}





/*
 * Quotient in unsigned division of x by y
 */
uint64_t bvconst64_udiv2z(uint64_t x, uint64_t y, uint32_t n) {
  uint64_t q;

  assert(0 < n && n <= 64);
  assert(x == norm64(x, n) && y == norm64(y, n));

  q = mask64(n); // all ones = quotient in x/0
  if (y != 0) {
    q = x/y;
  }
  assert(q == norm64(q, n));

  return q;
}


/*
 * Remainder in unsigned division of x by y
 */
uint64_t bvconst64_urem2z(uint64_t x, uint64_t y, uint32_t n) {
  uint64_t r;

  assert(0 < n && n <= 64);
  assert(x == norm64(x, n) && y == norm64(y, n));

  r = x; // remainder in x/0
  if (y != 0) {
    r %= y;
  }
  assert(r == norm64(r, n));

  return r;
}



/*
 * Quotient in the signed division of x by y,
 * with rounding towards 0.
 */
uint64_t bvconst64_sdiv2z(uint64_t x, uint64_t y, uint32_t n) {
  int64_t sx, sy, q;

  assert(0 < n && n <= 64);
  assert(x == norm64(x, n) && y == norm64(y, n));

  sx = signed_int64(x, n);
  sy = signed_int64(y, n);

  if (sy == 0) {
    // division by 0
    if (sx >= 0) {
      q = -1;
    } else {
      q = 1;
    }
  } else {
    q = sx/sy;
  }

  return norm64((uint64_t) q, n);
}



/*
 * Remainder in the signed division of x by y,
 * with rounding towards 0.
 */
uint64_t bvconst64_srem2z(uint64_t x, uint64_t y, uint32_t n) {
  int64_t sx, sy, r;

  assert(0 < n && n <= 64);
  assert(x == norm64(x, n) && y == norm64(y, n));

  sx = signed_int64(x, n);
  sy = signed_int64(y, n);

  r = sx; // remainder in sx/0 is sx
  if (sy != 0) {
    r %= sy;
  }

  return norm64((uint64_t) r, n);
}


/*
 * Remainder in the signed division of x by y,
 * with rounding towards minus infinity.
 */
uint64_t bvconst64_smod2z(uint64_t x, uint64_t y, uint32_t n) {
  int64_t sx, sy, q, r;

  assert(0 < n && n <= 64);
  assert(x == norm64(x, n) && y == norm64(y, n));

  sx = signed_int64(x, n);
  sy = signed_int64(y, n);

  r = sx; // remainder in sx/0 is sx
  if (sy != 0) {
    q = sx/sy;
    r = sx - q * sy;
    if (r != 0 && (is_neg64(x, n) != is_neg64(y, n))) {
      /*
       * x and y have opposite signs so the rational (x/y)
       * is negative. Then fdiv(sx, sy) is q-1 and we
       * must correct r.
       */
      r += sy;
    }
  }

  return norm64((uint64_t) r, n);
}


/*
 * STRING PARSING
 */

/*
 * Convert a string of '0's and '1's to a constant
 * - n = number of bits (n must be between 1 and 64)
 * - s must be at least n character long.
 *
 * Read the first n characters of s. All must be '0' and '1'
 * - the string is interpreted as a big-endian format: the
 *   first character is the high order bit.
 *
 * If the string format is wrong, return -1 and leave *a unchanged.
 * Otherwise, return 0 and store the result in *a (normalized modulo 2^n).
 */
int32_t bvconst64_set_from_string(uint64_t *a, uint32_t n, char *s) {
  uint64_t x;
  char c;

  assert(0 < n && n <= 64);

  x = 0;
  do {
    n --;
    c = *s;
    s ++;
    if (c == '1') {
      x = (x << 1) | 1;
    } else if (c == '0') {
      x = (x << 1);
    } else {
      return -1;
    }
  } while (n > 0);

  *a = x;

  return 0;
}


/*
 * Convert a string interpreted as an hexadecimal number to a constant.
 * - n = number of characters to read (n must be between 1 and 16)
 * - s must be at least n character long.
 *
 * Read the first n characters of s.
 * All must be in the ranges '0' to '9' or 'a' to 'f' or 'A' to 'F'.
 * The string is read in big-endian format: first character defines
 * the four high-order bits.
 *
 * Return -1 if the format is wrong (and leave *a unchanged).
 * Return 0 otherwise and store the result in a, normalized modulo 2^4n.
 */
static uint32_t hextoint(char c) {
  if ('0' <= c && c <= '9') {
    return c - '0';
  } else if ('a' <= c && c <= 'f') {
    return 10 + (c - 'a');
  } else {
    assert('A' <= c && c <= 'F');
    return 10 + (c - 'A');
  }
}

int32_t bvconst64_set_from_hexa_string(uint64_t *a, uint32_t n, char *s) {
  uint64_t x;
  uint32_t hex;
  char c;

  assert(0 < n && n <= 16);

  x = 0;
  do {
    c = *s;
    s ++;
    if (isxdigit((int) c)) {
      hex = hextoint(c);
      assert(0 <= hex && hex < 16);
      // set bits 4n-1 to 4n-4
      x = (x << 4) | hex;
      n --;
    } else {
      // error
      return -1;
    }
  } while (n > 0);

  *a = x;

  return 0;
}



/*
 * Convert the n low-order bits of a rational q to a bitvector
 * constant of n-bits
 * - q must be a non-negative integer
 */
uint64_t bvconst64_from_q(uint32_t n, rational_t *q) {
  uint32_t aux[2];
  uint64_t x;

  assert(1 <= n && n <= 64);

  bvconst_set_q(aux, 2, q);
  x = ((uint64_t) aux[0]) | (((uint64_t) aux[1]) << 32);

  return norm64(x, n);
}




/*
 * Display a in binary format. n = number of bits
 */
void bvconst64_print(FILE *f, uint64_t a, uint32_t n) {
  assert(1 <= n && n <= 64);

  fprintf(f, "0b");
  do {
    n --;
    fprintf(f, "%u", (unsigned) tst_bit64(a, n));
  } while (n > 0);
}


/*
 * Store the n lowest order bits of bv into a
 * - as an integer array: a[i] = bit i of bv (either 0 or 1)
 * - n must be positive and no more than 64
 */
void bvconst64_get_array(uint64_t bv, int32_t *a, uint32_t n) {
  uint32_t i;

  assert(0 < n && n <= 64);

  for (i=0; i<n; i++) {
    a[i] = tst_bit64(bv, i);
  }
}
