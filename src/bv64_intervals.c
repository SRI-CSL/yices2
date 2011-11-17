/*
 * INTERVALS FOR BIT-VECTOR VALUES
 */

#include "bv64_intervals.h"


/*
 * SUM OF INTERVALS
 */

/*
 * Compute the best overapproximation of [a.low + b.low, a.high + b.high] modulo 2^n
 * - n = bitsize of a and b
 * - a and b must have the same bitsize and be normalized
 * - the result is stored in a
 * - Unsigned version: there's loss of precision if 
 *   (a.low + b.low < 2^n <= a.high + b.high).
 *   In this case, the result is set to [0, 2^n-1]
 */
void bv64_interval_add_u(bv64_interval_t *a, bv64_interval_t *b) {
  uint32_t n;

  n = a->nbits;

  assert(1 <= n && n <= 64 && n == b->nbits);
  assert(bv64_interval_is_normalized(a) && a->low <= a->high);
  assert(bv64_interval_is_normalized(b) && b->low <= b->high);

  a->low = norm64(a->low + b->low, n);
  a->high = norm64(a->high + b->high, n);
  if (a->high < b->high && a->low >= b->low) {
    /* 
     * overflow in a->high
     * no overflow in a->low 
     * so the domain D is [a->low, 0b1111] U [0b0000, a->high]
     * the enclosing interval for D is [0b0000, 0b1111]
     */
    a->low = 0;
    a->high = mask64(n);
  }

  assert(bv64_interval_is_normalized(a) && a->low <= a->high);
}


/*
 * Underflow and overflow detection for a = b + c mod 2^n signed
 * - a, b, c are 2's complement n-bits integer
 * - there's underflow if (b < 0) and (c < 0) and (a >= 0)
 * - there's overflow  if (b >= 0) and (c >= 0) and (a < 0)
 */
static inline bool add_underflow64(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  assert(a == ((b + c) & mask64(n)));
  return is_neg64(b, n) && is_neg64(c, n) && is_pos64(a, n);
}

static inline bool add_overflow64(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  assert(a == ((b + c) & mask64(n)));
  return is_pos64(b, n) && is_pos64(c, n) && is_neg64(a, n);
}




/*
 * Bext overapproximation for [a.low + b.low, a.high + b.high] modulo 2^n
 * Signed version
 */
void bv64_interval_add_s(bv64_interval_t *a, bv64_interval_t *b) {
  uint64_t low, high;
  uint32_t n;

  n = a->nbits;

  assert(1 <= n && n <= 64 && n == b->nbits);
  assert(bv64_interval_is_normalized(a) && signed64_le(a->low, a->high, n));
  assert(bv64_interval_is_normalized(b) && signed64_le(b->low, b->high, n));

  low = norm64(a->low + b->low, n);    // low = (a.low + b.low) mod 2^n
  high = norm64(a->high + b->high, n); // high = (a.high + b.high) mod 2^n

  /*
   * The interval [low, high] is good unless
   * 1) there's underflow on low and not on high
   * 2) there's overflow on high and not on low
   */
  if ((add_underflow64(low, a->low, b->low, n) && !add_underflow64(high, a->high, b->high, n))
      || (add_overflow64(high, a->high, b->high, n) && !add_overflow64(low, a->low, b->low, n))) {
    low = min_signed64(n);
    high = max_signed64(n);
  }

  a->low = low;
  a->high = high;

  assert(bv64_interval_is_normalized(a) && signed64_le(a->low, a->high, n));
}


/*
 * DIFFERENCE
 */

 /*
 * Best possible overapproximation to [a.low - b.high, a.high - b.low]
 * - the result is stored un a
 * - there's loss of precision if a.low < b.high and a.high >= b.low
 */
void bv64_interval_sub_u(bv64_interval_t *a, bv64_interval_t *b) {
  uint32_t n;

  n = a->nbits;

  assert(1 <= n && n <= 64 && n == b->nbits);
  assert(bv64_interval_is_normalized(a) && a->low <= a->high);
  assert(bv64_interval_is_normalized(b) && b->low <= b->high);

  if (a->low < b->high && a->high >= b->low) {
    // underflow on a->low - b->high, not on a->high - b->low
    a->low = 0;
    a->high = mask64(n);
  } else {
    a->low = norm64(a->low - b->high, n);
    a->high = norm64(a->high - b->low, n);
  }

  assert(bv64_interval_is_normalized(a) && a->low <= a->high);
}




/*
 * Overflow/underflow detection for a = b - c mod 2^n:
 * - underflow if b<0, c>=0, and a >= 0
 * - overflow if b>=0, c<0, and a < 0
 */
static inline bool sub_underflow64(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  assert(a == ((b - c) & mask64(n)));
  return is_neg64(b, n) && is_pos64(c, n) && is_pos64(a, n);
}

static inline bool sub_overflow64(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  assert(a == ((b - c) & mask64(n)));
  return is_pos64(b, n) && is_neg64(c, n) && is_neg64(a, n);
}

/*
 * Same thing for a signed interval
 */
void bv64_interval_sub_s(bv64_interval_t *a, bv64_interval_t *b) {
  uint64_t low, high;
  uint32_t n;

  n = a->nbits;

  assert(1 <= n && n <= 64 && n == b->nbits);
  assert(bv64_interval_is_normalized(a) && signed64_le(a->low, a->high, n));
  assert(bv64_interval_is_normalized(b) && signed64_le(b->low, b->high, n));

  low = norm64(a->low - b->high, n);   // low = (a.low - b.high) mod 2^n
  high = norm64(a->high - b->low, n);  // high = (a.high - a.low) mod 2^n

  /*
   * The interval [low, high] is good unless
   * 1) there's underflow on low and not on high
   * 2) there's overflow on high and not on low
   */
  if ((sub_underflow64(low, a->low, b->high, n) && !sub_underflow64(high, a->high, b->low, n))
      || (sub_overflow64(high, a->high, b->low, n) && !sub_overflow64(low, a->low, b->high, n))) {
    low = min_signed64(n);
    high = max_signed64(n);
  }

  a->low = low;
  a->high = high;

  assert(bv64_interval_is_normalized(a) && signed64_le(a->low, a->high, n));
}

