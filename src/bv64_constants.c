/*
 * OPERATIONS ON SMALL BITVECTOR CONSTANTS
 */

#include "bv64_constants.h"

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


