/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>

#include "terms/bv64_constants.h"
#include "terms/bv64_interval_abstraction.h"
#include "utils/int_powers.h"



/*
 * ARITHMETIC ON SIGNED K-BIT CONSTANTS
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
    *overflow = (x < 0 && y < 0 && s >= 0) || (x >= 0 && y >= 0 && s < 0);
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
 * Max of two bitsizes
 */
static inline uint32_t max(uint32_t x, uint32_t y) {
  return (x > y) ? x : y;
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
 * Max of xy and uv
 */
static int64_t max_mul(int64_t x, int64_t y, int64_t u, int64_t v, bool *overflow) {
  int64_t p, q;

  p = mul(x, y, overflow);
  if (! *overflow) {
    q = mul(u, v, overflow);
    if (p < q) p = q;
  }
  return p;
}


/*
 * Min of xy and uv
 */
static int64_t min_mul(int64_t x, int64_t y, int64_t u, int64_t v, bool *overflow) {
  int64_t p, q;

  p = mul(x, y, overflow);
  if (! *overflow) {
    q = mul(u, v, overflow);
    if (p > q) p = q;
  }
  return p;
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
 * Number of significant bits in x
 * - if the result is k then -2^(k-1) <= x < 2^(k-1)
 */
static uint32_t num_significant_bits(int64_t x) {
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


/*
 * Number of bits to represent the interval [low, high]
 */
static uint32_t interval_bitsize(int64_t low, int64_t high) {
  uint32_t kl, kh;

  kl = num_significant_bits(low);
  kh = num_significant_bits(high);
  return (kl < kh) ? kh : kl;
}



#ifndef NDEBUG
/*
 * Consistency checks
 */
static bool bv64_consistent_sign(bv64_abs_t *a) {
  if (a->low >= 0) {
    return a->sign == sign_zero;
  } else if (a->high < 0) {
    return a->sign == sign_one;
  } else {
    return true;
  }
}

static bool bv64_consistent_nbits(bv64_abs_t *a) {
  uint32_t k, lk, hk;

  k = a->nbits;
  lk = num_significant_bits(a->low);
  assert(1 <= lk && lk <= 64);
  hk = num_significant_bits(a->high);
  assert(1 <= lk && lk <= 64);

  return (k == lk && k >= hk) || (k == hk && k >= lk);
}

static bool bv64_abs_consistent(bv64_abs_t *a) {
  return a->low <= a->high && bv64_consistent_sign(a) && bv64_consistent_nbits(a);
}
#endif



/*
 * Abstraction of a constant c.
 * - n = number of bits in c
 * - n must be positive and no more than 64
 */
void bv64_abs_constant(bv64_abs_t *a, uint64_t c, uint32_t n) {
  int64_t sc;
  uint32_t k;

  assert(1 <= n && n <= 64);

  k = n - 1;

  if (tst_bit64(c, k)) {
    // the sign bit is one
    while (k > 0 && tst_bit64(c, k - 1)) {
      k --;
    }
    a->nbits = k + 1;
    a->sign = sign_one;
    sc = (int64_t) (c | ~mask64(n)); // sign extend
    a->low = sc;
    a->high = sc;
  } else {
    // the sign bit is zero
    while (k > 0 && !tst_bit64(c, k-1)) {
      k --;
    }
    a->nbits = k + 1;
    a->sign = sign_zero;
    sc = (int64_t) c;
    a->low = sc;
    a->high = sc;
  }

  assert(bv64_abs_consistent(a));
}


/*
 * Special cases: constant 0, +1, and -1
 */
void bv64_abs_zero(bv64_abs_t *a) {
  a->nbits = 1;
  a->sign = sign_zero;
  a->low = 0;
  a->high = 0;

  assert(bv64_abs_consistent(a));
}

void bv64_abs_one(bv64_abs_t *a) {
  a->nbits = 2;
  a->sign = sign_zero;
  a->low = 1;
  a->high = 1;

  assert(bv64_abs_consistent(a));
}

void bv64_abs_minus_one(bv64_abs_t *a) {
  a->nbits = 1;
  a->sign = sign_one;
  a->low = -1;
  a->high = -1;

  assert(bv64_abs_consistent(a));
}


/*
 * Default interval when we know nothing (except the number of bits).
 */
void bv64_abs_default(bv64_abs_t *a, uint32_t n) {
  assert(1 <= n && n <= 64);

  a->nbits = n;
  a->sign = sign_undef;
  a->low = min_int(n);
  a->high = max_int(n);

  assert(bv64_abs_consistent(a));
}

/*
 * Checks whether a is more precise than the full interval of n bits
 */
bool bv64_abs_nontrivial(bv64_abs_t *a, uint32_t n) {
  assert(bv64_abs_consistent(a));

  return a->nbits<n || 
    (a->nbits == n && (a->low > min_int(n) || a->high < max_int(n) || a->sign != sign_undef));
}


/*
 * Least precise interval
 */
static void bv64_top_abs(bv64_abs_t *a) {
  a->nbits = 64;
  a->sign = sign_undef;
  a->low = INT64_MIN;
  a->high = INT64_MAX;

  assert(bv64_abs_consistent(a));
}


/*
 * Flip sign
 */
static inline int32_t negate_sign(int32_t s) {
  assert(s >= 0);
  return s ^ 1;
}


/*
 * Check whether a is the interval [0,0]
 */
static inline bool bv64_abs_is_zero(const bv64_abs_t *a) {
  return a->low == 0 && a->high == 0;
}


/*
 * Check whether a and b have opposite signs
 */
static inline bool bv64_abs_opposite_signs(const bv64_abs_t *a, const bv64_abs_t *b) {
  return a->sign >= 0 && b->sign == negate_sign(a->sign);
}


/*
 * Abstraction of an array u of n bits.
 * - n must be positive and no more than 64
 *
 * We want this to work for both arrays of Boolean terms and arrays of
 * literals.  Terms and literals use the same conventions:
 * - they are represented by signed 32bit integers
 * - the null term or literal is denoted by -1
 * - negating a term or a literal corresponds to flipping the least
 *   significant bit of the index.
 * The only difference between terms and literals is the encoding of
 * true and false: 
 * - true_term = 2 and true_literal = 0
 * - false_term = 3 and false_literal = 1
 *
 * To deal with both cases, this function takes an extra parameter:
 * zero, which must be the encoding of false.
 */
void bv64_abs_array(bv64_abs_t *a, int32_t zero, const int32_t *u, uint32_t n) {
  uint32_t i, k;
  int32_t s, one;
  uint64_t lb, ub;
  int64_t s_min, s_max;

  assert(1 <= n && n <= 64 && zero >= 0);

  one = negate_sign(zero);

  k = n-1;
  s = u[k];
  while (k > 0 && u[k-1] == s) {
    k --;
  }

  a->nbits = k + 1;
  if (s == zero) {
    a->sign = sign_zero;
  } else if (s == one) {
    a->sign = sign_one;
  } else {
    a->sign = s;
  }

  /*
   * Upper and lower bounds on u:
   * - u = -2^k s + 2^(k-1) * u[k-1] + ... + 2 * u[1] + u[0]
   * - we use s_min <= -2^k <= s_max
   *   and lb <= 2^(k-1) * u[k-1] + ... + 2 * u[1] + u[0]
   */
  assert(k <= 63);

  s_min = min_int(k+1); // -2^(k)
  s_max = 0;
  if (s == zero) {
    s_min = s_max; // both are 0
  } else if (s == one) {
    s_max = s_min; // both are -2^k
  }

  if (k == 0) {
    lb = 0;
    ub = 0;
  } else {
    lb = 0;
    ub = mask64(k); // all bits set to 1
    for (i=0; i<k; i++) {
      if (u[i] == zero) {
	ub = clr_bit64(ub, i);
      } else if (u[i] == one) {
	lb = set_bit64(lb, i);
      }
    }
  }

  assert(lb <= ub && ub <= ((uint64_t) INT64_MAX));

  a->low = s_min + (int64_t) lb;
  a->high = s_max + (int64_t) ub;

  assert(bv64_abs_consistent(a));  
}


/*
 * Abstraction for (- a): 
 * - the result is stored in place
 */
void bv64_abs_negate(bv64_abs_t *a) {  
  int64_t low, high;
  uint32_t k;
  bool overflow;

  k = a->nbits;

  low = - a->high;
  high = opposite(a->low, k, &overflow);
  if (overflow && k >= 64) {
    bv64_top_abs(a);
    return;
  }

  a->nbits = interval_bitsize(low, high);
  a->low = low;
  a->high = high;
  if (low >= 0) {
    a->sign = sign_zero;
  } else if (high < 0) {
    a->sign = sign_one;
  } else {
    // the new interval [-high, -low] contains 0 so we've lost
    // the sign information (even if we knew the sign of a).
    a->sign = sign_undef;
  }

  assert(bv64_abs_consistent(a));
}


/*
 * Abstraction for (a * c) where c is an n-bit constant
 */
void bv64_abs_mul_const(bv64_abs_t *a, uint64_t c, uint32_t n) {
  int64_t low, high, sc;
  bool ovlow, ovhigh;
  uint32_t k;

  assert(1 <= n && n <= 64 && c == norm64(c, n));

  // special case
  if (c == 0) {
    bv64_abs_zero(a);
    return;
  }


  k = n-1;
  // sign extend c to a 64bit constant
  if (tst_bit64(c, k)) {
    sc = (int64_t) (c | ~mask64(n)); // sign extend
    assert(sc < 0);
    low = mul(a->high, sc, &ovlow);
    high = mul(a->low, sc, &ovhigh);
  } else {
    sc = (int64_t) c;
    assert(sc > 0);
    low = mul(a->low, sc, &ovlow);
    high = mul(a->high, sc, &ovhigh);
  }

  if (ovlow || ovhigh) {
    bv64_top_abs(a);
    return;
  } 

  a->nbits = interval_bitsize(low, high);
  a->low = low;
  a->high = high;
  if (low >= 0) {
    a->sign = sign_zero;
  } else if (high < 0) {
    a->sign = sign_one;
  } else if (sc < 0) {
    // [low, high] contains 0 so even if we knew a's sign
    // we've lost the information
    a->sign = sign_undef;
  }
  // if sc>0, we keep a->sign unchanged

  assert(bv64_abs_consistent(a));
}


/*
 * Abstraction for (a + b)
 * - the result is stored in a
 *
 * If a->sign == b->sign then the sign is preserved
 * (also if a->sign is sign_undef)
 */
void bv64_abs_add(bv64_abs_t *a, const bv64_abs_t *b) {
  int64_t low, high;
  uint32_t k;
  bool low_overflow, high_overflow;

  k = max(a->nbits, b->nbits);
  high = sum(a->high, b->high, k, &high_overflow);
  low = sum(a->low, b->low, k, &low_overflow);
  if ((high_overflow || low_overflow) && k >= 64) {
    bv64_top_abs(a);
    return;
  }

  a->nbits = interval_bitsize(low, high);
  a->low = low;
  a->high = high;

  if (low >= 0) {
    a->sign = sign_zero;
  } else if (high < 0) {
    a->sign = sign_one;
  } else if (a->sign != b->sign) {
    a->sign = sign_undef;
  }
  
  assert(bv64_abs_consistent(a));
}


/*
 * Abstraction for (a - b)
 * - the result is stored in a
 *
 * If a and b have opposite signs then the result
 * has the same sign as a.
 */
void bv64_abs_sub(bv64_abs_t *a, const bv64_abs_t *b) {
  int64_t low, high;
  uint32_t k;
  bool low_overflow, high_overflow;

  k = max(a->nbits, b->nbits);
  high = diff(a->high, b->low, k, &high_overflow);
  low = diff(a->low, b->high, k, &low_overflow);
  if ((high_overflow || low_overflow) && k >= 64) {
    bv64_top_abs(a);
    return;
  }

  a->nbits = interval_bitsize(low, high);
  a->low = low;
  a->high = high;

  if (low >= 0) {
    a->sign = sign_zero;
  } else if (high < 0) {
    a->sign = sign_one;
  } else if (bv64_abs_opposite_signs(a, b)) {
    a->sign = sign_undef;
  }
  
  assert(bv64_abs_consistent(a));
}


/*
 * Abstraction for (a * b)
 */
void bv64_abs_mul(bv64_abs_t *a, const bv64_abs_t *b) {
  int64_t low, high;
  bool ovlow, ovhigh;
  int32_t sign;

  // special cases: a = [0,0] or b = [0,0]
  if (bv64_abs_is_zero(a)) {
    return;    
  }
  if (bv64_abs_is_zero(b)) {
    bv64_abs_zero(a);
    return;
  }

  // a is [L1, H1], b is [L2, H2]
  if (a->sign == sign_zero) {
    if (b->sign == sign_zero) {
      // 0 <= [L1, H1] and 0 <= [L2, H2], the result is [L1.L2, H1.H2]
      low = mul(a->low, b->low, &ovlow);     // L1.L2 >= 0
      high = mul(a->high, b->high, &ovhigh); // H1.H2 > 0
      sign = sign_zero;
    } else if (b->sign == sign_one) {
      // 0 <= [L1, H1] and [L2, H2] < 0, the result is [H1.L2, L1.H2]
      low = mul(a->high, b->low, &ovlow);   // H1.L2 < 0 (because H1>0)
      high = mul(a->low, b->high, &ovhigh); // L1.H2 <= 0
      sign = (a->low == 0) ? sign_undef : sign_one;
    } else {
      // 0 <= [L1, H1] and L2 < 0 <= H2, the result is [H1.L2, H1.H2]
      low = mul(a->high, b->low, &ovlow);    // H1.L2 < 0 (because H1>0)
      high = mul(a->high, b->high, &ovhigh); // H1.H2 >= 0
      sign = (a->low == 0) ? sign_undef : b->sign; 
    }
  } else if (a->sign == sign_one) {
    if (b->sign == sign_zero) {
      // [L1, H1] < 0 and 0 <= [L2, H2], the result is [L1.H2, H1.L2]
      low = mul(a->low, b->high, &ovlow);    // L1.H2 < 0 (because H2>0)
      high = mul(a->high, b->low, &ovhigh);  // H1.L2 <= 0
      sign = (b->low == 0) ? sign_undef : sign_one;
    } else if (b->sign == sign_one) {
      // [L1, H1] < 0 and [L2, H2] < 0, the result is [H1.H2, L1.L2]
      low = mul(a->high, b->high, &ovlow);   // H1.H2 > 0
      high = mul(a->low, b->low, &ovhigh);   // L1.L2 > 0
      sign = sign_zero;
    } else {
      // [L1, H1] < 0 and L2 < 0 <= H2, the result is [L1.H2, L1.L2]
      low = mul(a->low, b->high, &ovlow);    // L1.H2 <= 0
      high = mul(a->low, b->low, &ovhigh);   // L1.L2 > 0
      sign = (low == 0) ? sign_zero : sign_undef;
    }
  } else {
    if (b->sign == sign_zero) {
      // L1 < 0 <= H1 and 0 <= [L2, H2], the result is [L1.H2, H1.H2]
      low = mul(a->low, b->high, &ovlow);     // L1.H2 < 0 since H2>0
      high = mul(a->high, b->high, &ovhigh);  // H1.H2 >= 0
      sign = (b->low == 0) ? sign_undef : a->sign;
    } else if (b->sign == sign_one) {
      // L1 < 0 <= H1 and [L2, H2] < 0, the result is [H1.L2, L1.L2]
      low = mul(a->high, b->low, &ovlow);     // H1.L2 <= 0
      high = mul(a->low, b->low, &ovhigh);    // L1.L2 > 0
      sign = (low == 0) ? sign_zero : sign_undef;
    } else if (b->sign == a->sign && a->sign != sign_undef) {
      // L1 < 0 <= H1 and L2 < 0 <= H2, both vectors have the same sign
      // the result is [0, max(L1.L2, H1.H2)]
      low = 0; 
      ovlow = false;
      high = max_mul(a->low, b->low, a->high, b->high, &ovhigh);
      sign = sign_zero;
    } else if (bv64_abs_opposite_signs(a, b)) {
      // L1 < 0 <= H1 and L2 < 0 <= H2, vectors of opposite signs
      // the result is [min(L1.H2, H1.L2), 0]
      // we have L1.H2 <= 0 and H1.L2 <= 0
      low = min_mul(a->low, b->high, a->high, b->low, &ovlow);
      high = 0;
      ovhigh = false;
      sign = (low == 0) ? sign_zero : sign_undef;
    } else {
      // L1 < 0 <= H1 and L2 < 0 <= H2,
      // the result is [min(L1.H2, H1.L2), max(L1.L2, H1.H2)]
      // we have L1.H2 <= 0 and H1.L2 <= 0 so the min may be 0
      low = min_mul(a->low, b->high, a->high, b->low, &ovlow);
      high = max_mul(a->low, b->low, a->high, b->high, &ovhigh);
      sign = (low == 0) ? sign_zero : sign_undef;
    }
  }

  if (ovlow || ovhigh) {
    bv64_top_abs(a);
  } else {
    a->low = low;
    a->high = high;
    a->sign = sign;
    a->nbits = interval_bitsize(low, high);
  }

  assert(bv64_abs_consistent(a));
}


/*
 * Abstraction for a^d
 */
void bv64_abs_power(bv64_abs_t *a, uint32_t d) {
  int64_t low, high;
  uint64_t abs_l;
  bool ovlow, ovhigh;
  int32_t sign;  
  
  assert(bv64_abs_consistent(a));

  if ((d & 1) == 0) {
    // even power: the result is non-negative
    sign = sign_zero;
    if (a->sign == sign_zero) {
      // 0 <= [L, H]: result is [L^d, H^d]
      low = power(a->low, d, &ovlow);
      high = power(a->high, d, &ovhigh);      
    } else if (a->sign == sign_one) {
      // [L, H] < 0: result is [H^d, L^d]
      low = power(a->high, d, &ovlow);
      high = power(a->low, d, &ovhigh);
    } else {
      // L < 0 <= H, the result is [0, max(L^d, H^d)]
      low = 0;
      ovlow = false;
      // set high to either L or H, whichever has largest absolute value
      // then compute high^d
      abs_l = - a->low;
      high = (abs_l < (uint64_t) a->high) ? a->high : a->low;
      high = power(high, d, &ovhigh);
    }
    
  } else {
    // odd power: the sing is unchanged
    low = power(a->low, d, &ovlow);
    high = power(a->high, d, &ovhigh);
    sign = a->sign;
  }

  if (ovlow || ovhigh) {
    bv64_top_abs(a);
  } else {
    a->low = low;
    a->high = high;
    a->sign = sign;
    a->nbits = interval_bitsize(low, high);
  }

  assert(bv64_abs_consistent(a));
}

