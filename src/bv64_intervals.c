/*
 * INTERVALS FOR BIT-VECTOR VALUES
 */

#include "bv64_intervals.h"


/*
 * OVERFLOW/UNDERFLOW DETECTION
 */

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
 * INTERVAL COMPUTATION
 */

/*
 * Compute the interval that encloses the set 
 *   S = { (x1 + x2) mod 2^n | a.low <= x1 <= a.high and l <= x2 <= u }
 *
 * Store the result in a:
 *   a.low := min(S)
 *   a.high := max(S)
 *
 * If (a.low + l) < 2^n <= (a.high + u) then
 *   min(S) is 0
 *   max(S) is 2^n-1
 * Otherwise
 *   min(S) is (a.low + l) mod 2^n 
 *   max(S) is (a.high + u) mod 2^n
 */
static void bv64_interval_add_u_core(bv64_interval_t *a, uint64_t l, uint64_t u, uint32_t n) {
  assert(1 <= n && n <= 64 && n == a->nbits);
  assert(bv64_interval_is_normalized(a) && a->low <= a->high);
  assert(l == norm64(l, n) && u == norm64(u, n) && l <= u);

  a->low = norm64(a->low + l, n);
  a->high = norm64(a->high + u, n);
  if (a->high < u && a->low >= l) {
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
 * Same thing for signed intervals
 */
static void bv64_interval_add_s_core(bv64_interval_t *a, uint64_t l, uint64_t u, uint32_t n) {
  uint64_t low, high;

  assert(1 <= n && n <= 64 && n == a->nbits);
  assert(bv64_interval_is_normalized(a) && signed64_le(a->low, a->high, n));
  assert(l == norm64(l, n) && u == norm64(u, n) && signed64_le(l, u, n));

  low = norm64(a->low + l, n);    // low = (a.low + l) mod 2^n
  high = norm64(a->high + u, n); // high = (a.high + u) mod 2^n

  /*
   * The interval [low, high] is good unless
   * 1) there's underflow on low and not on high
   * 2) there's overflow on high and not on low
   */
  if ((add_underflow64(low, a->low, l, n) && !add_underflow64(high, a->high, u, n))
      || (add_overflow64(high, a->high, u, n) && !add_overflow64(low, a->low, l, n))) {
    low = min_signed64(n);
    high = max_signed64(n);
  }

  a->low = low;
  a->high = high;

  assert(bv64_interval_is_normalized(a) && signed64_le(a->low, a->high, n));
}



/*
 * Interval enclosing the difference a - [l, u]
 *   D =  { (x1 - x2) mod 2^n | a.low <= x1 <= a.high and l <= x2 <= u }
 *
 * Store the result in a:
 *   a.low := min(D)
 *   a.high := max(D)
 *
 * If a.low < u and a.high >= l, we  have
 *   min(D) = 0
 *   max(D) = 2^n-1
 * Otherwise
 *   min(D) = (a.low - u) mod 2^n 
 *   max(D) = (a.high - l) mod 2^n
 */
static void bv64_interval_sub_u_core(bv64_interval_t *a, uint64_t l, uint64_t u, uint32_t n) {
  assert(1 <= n && n <= 64 && n == a->nbits);
  assert(bv64_interval_is_normalized(a) && a->low <= a->high);
  assert(l == norm64(l, n) && u == norm64(u, n) && l <= u);

  if (a->low < u && a->high >= l) {
    // underflow on a->low - u, not on a->high - l
    a->low = 0;
    a->high = mask64(n);
  } else {
    a->low = norm64(a->low - u, n);
    a->high = norm64(a->high - l, n);
  }

  assert(bv64_interval_is_normalized(a) && a->low <= a->high);
}


/*
 * Same thing for signed intervals
 */
static void bv64_interval_sub_s_core(bv64_interval_t *a, uint64_t l, uint64_t u, uint32_t n) {
  uint64_t low, high;

  assert(1 <= n && n <= 64 && n == a->nbits);
  assert(bv64_interval_is_normalized(a) && signed64_le(a->low, a->high, n));
  assert(l == norm64(l, n) && u == norm64(u, n) && signed64_le(l, u, n));

  low = norm64(a->low - u, n);   // low = (a.low - u) mod 2^n
  high = norm64(a->high - l, n);  // high = (a.high - l) mod 2^n

  /*
   * The interval [low, high] is good unless
   * 1) there's underflow on low and not on high
   * 2) there's overflow on high and not on low
   */
  if ((sub_underflow64(low, a->low, u, n) && !sub_underflow64(high, a->high, l, n))
      || (sub_overflow64(high, a->high, l, n) && !sub_overflow64(low, a->low, u, n))) {
    low = min_signed64(n);
    high = max_signed64(n);
  }

  a->low = low;
  a->high = high;

  assert(bv64_interval_is_normalized(a) && signed64_le(a->low, a->high, n));
}



void bv64_interval_add_u(bv64_interval_t *a, bv64_interval_t *b) {
  bv64_interval_add_u_core(a, b->low, b->high, b->nbits);
}

void bv64_interval_add_s(bv64_interval_t *a, bv64_interval_t *b) {
  bv64_interval_add_s_core(a, b->low, b->high, b->nbits);
}


void bv64_interval_sub_u(bv64_interval_t *a, bv64_interval_t *b) {
  bv64_interval_sub_u_core(a, b->low, b->high, b->nbits);
}

void bv64_interval_sub_s(bv64_interval_t *a, bv64_interval_t *b) {
  bv64_interval_sub_s_core(a, b->low, b->high, b->nbits);
}



/*
 * Best overapproximation of [a.low + c * b.low, a.high + c * b.high] modulo 2^n
 * - a and b must have the same bitsize and be normalized
 * - c must be normalized modulo 2^n too
 * - the result is stored in a
 * Unsigned version
 */
void bv64_interval_addmul_u(bv64_interval_t *a, bv64_interval_t *b, uint64_t c) {
  uint64_t l, u;
  uint32_t n;

  l = b->low;
  u = b->high;
  n = b->nbits;

  assert(c == norm64(c, n));

  // common cases: c == 1 or c == -1
  if (c == 1) {
    bv64_interval_add_u_core(a, l, u, n);
  } else if (c == mask64(n)) {
    bv64_interval_sub_u_core(a, l, u, n);
  } else {    
    // TBD: return the trivial interval for now
    a->low = 0;
    a->high = mask64(n);    
  }
}



/*
 * Best overapproximation of [a.low + c * b.low, a.high + c * b.high] modulo 2^n
 * - a and b must have the same bitsize and be normalized
 * - c must be normalized modulo 2^n too
 * - the result is stored in a
 * Signed version
 */
void bv64_interval_addmul_s(bv64_interval_t *a, bv64_interval_t *b, uint64_t c) {
  uint64_t l, u;
  uint32_t n;

  l = b->low;
  u = b->high;
  n = b->nbits;

  assert(c == norm64(c, n));

  // common cases: c == 1 or c == -1
  if (c == 1) {
    bv64_interval_add_s_core(a, l, u, n);
  } else if (c == mask64(n)) {
    bv64_interval_sub_s_core(a, l, u, n);
  } else {
    // TBD: return the trivial interval for now
    a->low = min_signed64(n);
    a->high = max_signed64(n);    
  }
}



