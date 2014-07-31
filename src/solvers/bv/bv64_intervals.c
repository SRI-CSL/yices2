/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * INTERVALS FOR BIT-VECTOR VALUES
 */

#include "terms/bv_constants.h"
#include "solvers/bv/bv64_intervals.h"


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
  return is_neg64(b, n) & is_neg64(c, n) & is_pos64(a, n);
}

static inline bool add_overflow64(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  assert(a == ((b + c) & mask64(n)));
  return is_pos64(b, n) & is_pos64(c, n) & is_neg64(a, n);
}


/*
 * Overflow/underflow detection for a = b - c mod 2^n:
 * - underflow if b<0, c>=0, and a >= 0
 * - overflow if b>=0, c<0, and a < 0
 */
static inline bool sub_underflow64(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  assert(a == ((b - c) & mask64(n)));
  return is_neg64(b, n) & is_pos64(c, n) & is_pos64(a, n);
}

static inline bool sub_overflow64(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  assert(a == ((b - c) & mask64(n)));
  return is_pos64(b, n) & is_neg64(c, n) & is_neg64(a, n);
}



/*
 * Compute a + b*c as a 128 bit unsigned integer
 * - the result is stored in r as an array of four 32-bit words
 * - r[0] = low-order word, r[3] = high-order word
 *   (cf. bv_constants.h)
 */
static void add_mul64(uint32_t r[4], uint64_t a, uint64_t b, uint64_t c) {
  uint32_t bb[4];
  uint32_t cc[4];

  // convert a, b, c to 128 bit (zero extend)
  bvconst_set64(r, 4, a);
  bvconst_set64(bb, 4, b);
  bvconst_set64(cc, 4, c);
  bvconst_addmul(r, 4, bb, cc);
}


/*
 * Same thing for a - b * c
 */
static void sub_mul64(uint32_t r[4], uint64_t a, uint64_t b, uint64_t c) {
  uint32_t bb[4];
  uint32_t cc[4];

  // convert a, b, c to 128 bit (zero extend)
  bvconst_set64(r, 4, a);
  bvconst_set64(bb, 4, b);
  bvconst_set64(cc, 4, c);
  bvconst_submul(r, 4, bb, cc);
}


/*
 * Compute (a + b*c) >> n
 * - a, b, and c must all be normalized modulo 2^n
 * - the result is returned normalized too
 */
static uint64_t add_mul_shift64(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  uint32_t aux[4];
  uint64_t r;

  assert(a == norm64(a, n) && b == norm64(b, n) && c == norm64(c, n));

  if (n <= 32) {
    r = (a + b * c) >> n;
  } else {
    assert(n <= 64);
    add_mul64(aux, a, b, c);
    bvconst_shift_right(aux, 2 * n, n, 0);
    r = bvconst_get64(aux);
  }

  assert(r == norm64(r, n));

  return r;
}


/*
 * Same thing for (a - b*c) >> n
 */
static uint64_t sub_mul_shift64(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  uint32_t aux[4];
  uint64_t r;

  assert(a == norm64(a, n) && b == norm64(b, n) && c == norm64(c, n));

  if (n <= 32) {
    r = (a - b * c) >> n;
  } else {
    assert(n <= 64);
    sub_mul64(aux, a, b, c);
    bvconst_shift_right(aux, 2 * n, n, 0);
    r = bvconst_get64(aux);
  }

  r = norm64(r, n);

  return r;
}




/*
 * Compute a + b*c as a 128 bit signed integer
 * - the result is stored in r as an array of four 32-bit words
 */
static void add_mul64_signed(uint32_t r[4], int64_t a, int64_t b, int64_t c) {
  uint32_t bb[4];
  uint32_t cc[4];

  // convert a, b, c to 128 bit (sign extend)
  bvconst_set64_signed(r, 4, a);
  bvconst_set64_signed(bb, 4, b);
  bvconst_set64_signed(cc, 4, c);
  bvconst_addmul(r, 4, bb, cc);
}


/*
 * (a + b * c) >> n when a, b, and c are signed integers
 */
static int64_t add_mul_shift64_signed(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  uint32_t aux[4];
  int64_t sa, sb, sc, r;

  assert(a == norm64(a, n) && b == norm64(b, n) && c == norm64(c, n));

  sa = signed_int64(a, n);
  sb = signed_int64(b, n);
  sc = signed_int64(c, n);

  if (n <= 32) {
    r = (sa + sb * sc) >> n;
  } else {
    assert(n <= 64);
    add_mul64_signed(aux, sa, sb, sc);
    bvconst_shift_right(aux, 2 * n, n, 0); // padding is irrelevant here
    r = (int64_t) bvconst_get64(aux);
  }

  return r;
}


#if 0

// NOT USED

/*
 * Compute a - b*c as a 128 bit signed integer
 */
static void sub_mul64_signed(uint32_t r[4], int64_t a, int64_t b, int64_t c) {
  uint32_t bb[4];
  uint32_t cc[4];

  // convert a, b, c to 128 bit (sign extend)
  bvconst_set64_signed(r, 4, a);
  bvconst_set64_signed(bb, 4, b);
  bvconst_set64_signed(cc, 4, c);
  bvconst_submul(r, 4, bb, cc);
}


/*
 * (a - b * c) >> n when a, b, and c are signed integers
 */
static int64_t sub_mul_shift64_signed(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  uint32_t aux[4];
  int64_t sa, sb, sc, r;

  assert(a == norm64(a, n) && b == norm64(b, n) && c == norm64(c, n));

  sa = signed_int64(a, n);
  sb = signed_int64(b, n);
  sc = signed_int64(c, n);

  if (n <= 32) {
    r = (sa - sb * sc) >> n;
  } else {
    assert(n <= 64);
    sub_mul64_signed(aux, sa, sb, sc);
    bvconst_shift_right(aux, 2 * n, n, 0); // padding is irrelevant here
    r = (int64_t) bvconst_get64(aux);
  }

  return r;
}

#endif



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
 * Overapproximation of [a.low + c * b.low, a.high + c * b.high] modulo 2^n
 * - a and b must have the same bitsize and be normalized
 * - c must be normalized modulo 2^n too
 * - the result is stored in a
 * Unsigned version
 */
void bv64_interval_addmul_u(bv64_interval_t *a, bv64_interval_t *b, uint64_t c) {
  uint64_t l, u, q1, q2;
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
    /*
     * We want an interval for (x + c y mod 2^n) where
     *     a.low <= x <= a.high   and   l <= y <= u.
     *
     * Let c' = (2^n - c) then (x + c y mod 2^n) == (x - c' y mod 2^n).
     *
     * If c < 2^(n-1) then c is smaller than c' in absolute value so
     * we use the inequalities: a.low + c l <= x + c y <= a.high + c u.
     *
     * If c >= 2^(n-1) then c' is smaller than c in absolute value so
     * we use: a.low - c' u <= x - c' y <= a.high - c' l.
     */
    if (is_pos64(c, n)) { // c < 2^(n-1)
      q1 = add_mul_shift64(a->low, l, c, n);   // q1 = quotient(a.low + c * b.low, 2^n)
      q2 = add_mul_shift64(a->high, u, c, n);  // q2 = quotient(a.high + c * b.high, 2^n)

      assert(q1 <= q2);

      /*
       * We know  q1 * 2^n <= a.low + c * l < (q1 + 1) * 2^n
       *     and  q2 * 2^n <= a.high + c * u < (q2 + 1) * 2^n
       *     and  a.low + c * l <= x + c * y <= a.high + c * u
       * If q1 = q2, we can conclude that
       *    (a.low + c*l) mod 2^n  <=  (x + c * y) mod 2^n <= (a.high + c * u) mod 2^n
       * Otherwise we return the trivial interval.
       */
      if (q1 == q2) {
        a->low = norm64(a->low + c * l,  n);
        a->high = norm64(a->high + c * u, n);
      } else {
        a->low = 0;
        a->high = mask64(n);
      }

    } else {
      c = norm64(-c, n); // this is c'
      q1 = sub_mul_shift64(a->low, u, c, n);
      q2 = sub_mul_shift64(a->high, l, c, n);

      assert(signed64_le(q1, q2, n));

      if (q1 == q2) {
        a->low = norm64(a->low - c * u, n);
        a->high = norm64(a->high - c * l, n);
      } else {
        a->low = 0;
        a->high = mask64(n);
      }
    }

    assert(bv64_interval_is_normalized(a) && a->low <= a->high);
  }
}



/*
 * Overapproximation of [a.low + c * b.low, a.high + c * b.high] modulo 2^n
 * - a and b must have the same bitsize and be normalized
 * - c must be normalized modulo 2^n too
 * - the result is stored in a
 * Signed version
 */
void bv64_interval_addmul_s(bv64_interval_t *a, bv64_interval_t *b, uint64_t c) {
  uint64_t l, u;
  int64_t q1, q2;
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
    if (is_pos64(c, n)) {
      q1 = add_mul_shift64_signed(a->low, l, c, n);
      q2 = add_mul_shift64_signed(a->high, u, c, n);
      l = norm64(a->low + c * l, n);
      u = norm64(a->high + c * u, n);
    } else {
      q1 = add_mul_shift64_signed(a->low, u, c, n);
      q2 = add_mul_shift64_signed(a->high, l, c, n);
      l = norm64(a->low + c * u, n);
      u = norm64(a->high + c * b->low, n);
    }

    if ((q1 == q2 && signed64_le(l, u, n)) ||
        (q1 == q2 - 1 && is_neg64(l, n) && is_pos64(u, n))) {
      a->low = l;
      a->high = u;
    } else {
      a->low = min_signed64(n);
      a->high = max_signed64(n);
    }

    assert(bv64_interval_is_normalized(a) && signed64_le(a->low, a->high, n));
  }
}



