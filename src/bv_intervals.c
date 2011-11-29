/*
 * INTERVALS OF BIT-VECTOR VALUES 
 */

#include "memalloc.h"
#include "bv_intervals.h"


/*
 * Initialization: don't allocate anything yet.
 * - nbits, width, and size are set to 0
 * - the arrays are allocated on the first call to resize
 */
void init_bv_interval(bv_interval_t *intv) {
  intv->low = NULL;
  intv->high = NULL;
  intv->nbits = 0;
  intv->width = 0;
  intv->size = 0;
}


/*
 * Free memory and reset
 */
void delete_bv_interval(bv_interval_t *intv) {
  safe_free(intv->low);
  safe_free(intv->high);
  intv->low = NULL;
  intv->high = NULL;
  intv->nbits = 0;
  intv->width = 0;
  intv->size = 0;
}


/*
 * Make sure array low/high are large enough to store n words
 * - n must be no more than BV_INTERVAL_MAX_SIZE
 */
static void bv_interval_set_size(bv_interval_t *intv, uint32_t n) {  
  if (intv->size < n) {
    if (n < BV_INTERVAL_DEF_SIZE) {
      n = BV_INTERVAL_DEF_SIZE;
    }
    assert(n <= BV_INTERVAL_MAX_SIZE); 
    intv->low = (uint32_t *) safe_realloc(intv->low, n * sizeof(uint32_t));
    intv->high = (uint32_t *) safe_realloc(intv->high, n * sizeof(uint32_t));
    intv->size = n;
  }
}


/*
 * Make sure the arrays low/high are large enough for n bits
 */
void resize_bv_interval(bv_interval_t *intv, uint32_t n) {
  uint32_t w;

  w = (n + 31) >> 5; // number of words = ceil(n/32)
  bv_interval_set_size(intv, w);
  assert(intv->size >= w);
  intv->nbits = n;
  intv->width = w;
}
 

/*
 * Initialize intv to [x, x]
 * - n must be positive
 * - x must be normalized modulo 2^n (cf. bv_constants.h)
 */
void bv_point_interval(bv_interval_t *intv, uint32_t *x, uint32_t n) {
  assert(n > 0 && bvconst_is_normalized(x, n));

  resize_bv_interval(intv, n);
  bvconst_set(intv->low, intv->width, x);
  bvconst_set(intv->high, intv->width, x);
}


/*
 * Initialize intv to [0, 0]
 * - n must be positive
 */
void bv_zero_interval(bv_interval_t *intv, uint32_t n) {
  assert(n > 0);

  resize_bv_interval(intv, n);
  bvconst_clear(intv->low, intv->width);
  bvconst_clear(intv->high, intv->width);
}


/*
 * Initialize to the interval [x, y] (unsigned)
 * - n must be positive
 * - x and y must be normalized modulo 2^n  
 * - x <= y must hold
 * - the arrays are resized if necessary
 */
void bv_interval_set_u(bv_interval_t *intv, uint32_t *x, uint32_t *y, uint32_t n) {
  assert(n > 0 && bvconst_is_normalized(x, n) && bvconst_is_normalized(y, n) &&
	 bvconst_le(x, y, n));

  resize_bv_interval(intv, n);
  bvconst_set(intv->low, intv->width, x);
  bvconst_set(intv->high, intv->width, y);
}


/*
 * Initialize to the interval [x, y] (signed)
 * - n must be positive
 * - x and y must be normalized modulo 2^n  
 * - x <= y must hold (2s'complement comparison)
 * - the arrays are resized if necessary
 */
void bv_interval_set_s(bv_interval_t *intv, uint32_t *x, uint32_t *y, uint32_t n) {
  assert(n > 0 && bvconst_is_normalized(x, n) && bvconst_is_normalized(y, n) && 
	 bvconst_sle(x, y, n));

  resize_bv_interval(intv, n);
  bvconst_set(intv->low, intv->width, x);
  bvconst_set(intv->high, intv->width, y);
}


/*
 * Initialize to the trivial interval (unsigned)
 * - n must be positive
 * - low is set to 0b000..0
 * - high is set to 0b111..1
 */
void bv_triv_interval_u(bv_interval_t *intv, uint32_t n) {
  assert(n > 0);

  resize_bv_interval(intv, n);
  bvconst_clear(intv->low, intv->width);
  bvconst_set_minus_one(intv->high, intv->width);
  bvconst_normalize(intv->high, n);
}


/*
 * Initialize to the trivial interval (signed)
 * - n must be positive
 * - low is set to 0b100..0
 * - high is set to 0b0111..1
 */
void bv_triv_interval_s(bv_interval_t *intv, uint32_t n) {
  assert(n > 0);

  resize_bv_interval(intv, n);
  bvconst_set_min_signed(intv->low, n);
  bvconst_set_max_signed(intv->high, n);
}


/*
 * Compute the interval that encloses the set S = [a.low, a.high] + [l, u]
 * - n = bitsize 
 * - l and u must be normalized modulo 2^n
 * - a must also be normalized and have nbits = n
 */
static void bv_interval_add_u_core(bv_interval_t *a, uint32_t *l, uint32_t *u, uint32_t n) {
  uint32_t w;

  assert(n > 0 && n == a->nbits);
  assert(bv_interval_is_normalized(a) && bvconst_le(a->low, a->high, n));
  assert(bvconst_is_normalized(l, n) && bvconst_is_normalized(u, n) && bvconst_le(l, u, n));

  w = a->width;
  assert(w == (n + 31) >> 5);

  bvconst_add(a->low, w, l);
  bvconst_add(a->high, w, u);
  bvconst_normalize(a->low, n);
  bvconst_normalize(a->high, n);

  if (bvconst_lt(a->high, u, n) && bvconst_le(a->low, l, n)) {
    // overvlow in a->high, no overflow in a->low so the 
    // enclosing interval is [0b000..., 0b111...]
    bvconst_clear(a->low, w);
    bvconst_set_minus_one(a->high, w);
    bvconst_normalize(a->high, n);
  }

  assert(bv_interval_is_normalized(a) && bvconst_le(a->low, a->high, n));
}



/*
 * Check for overflow/underflow in a := a0 + b
 * - sa = sign of a0 before the operation
 * - n = number of bits in a and b
 * - overflow: if (a0 >= 0) and (b >= 0) and (a < 0)
 * - undeflow: if (a0 < 0) and (b < 0) and (a >= 0)
 */
static inline bool add_overflow(uint32_t *a, uint32_t *b, bool sa, uint32_t n) {
  // sign bit of a0 = 0, sign bit of b = 0, sign bit of a = 1
  return !sa & !bvconst_tst_bit(b, n-1) & bvconst_tst_bit(a, n-1);
}

static inline bool add_underflow(uint32_t *a, uint32_t *b, bool sa, uint32_t n) {
  // sign bit of a0 = 1, sign bit of b = 1, sign bit of a = 0
  return sa & bvconst_tst_bit(b, n-1) & !bvconst_tst_bit(a, n-1);
}


/*
 * Sum of a and [l, n] for signed intervals
 */
static void bv_interval_add_s_core(bv_interval_t *a, uint32_t *l, uint32_t *u, uint32_t n) {
  uint32_t w;
  bool s_low, s_high;

  assert(n > 0 && n == a->nbits);
  assert(bv_interval_is_normalized(a) && bvconst_sle(a->low, a->high, n));
  assert(bvconst_is_normalized(l, n) && bvconst_is_normalized(u, n) && bvconst_sle(l, u, n));

  w = a->width;
  assert(w == (n + 31) >> 5);

  /*
   * for overflow/underflow detection, store the sign of a->low and a->high
   */
  s_low = bvconst_tst_bit(a->low, n-1);
  s_high = bvconst_tst_bit(a->high, n-1);

  bvconst_add(a->low, w, l);
  bvconst_add(a->high, w, u);
  bvconst_normalize(a->low, n);
  bvconst_normalize(a->high, n);
  
  if ((add_underflow(a->low, l, s_low, n) && !add_underflow(a->high, u, s_high, n))
      || (add_overflow(a->high, u, s_high, n) && !add_overflow(a->low, l, s_low, n))) {
    bvconst_set_min_signed(a->low, n);
    bvconst_set_max_signed(a->high, n);
  }
  
  assert(bv_interval_is_normalized(a) && bvconst_sle(a->low, a->high, n));
}





/*
 * Compute the enclosing interval for a - [l, u] (unsigned intervals)
 */
static void bv_interval_sub_u_core(bv_interval_t *a, uint32_t *l, uint32_t *u, uint32_t n) {
  uint32_t w;

  assert(n > 0 && n == a->nbits);
  assert(bv_interval_is_normalized(a) && bvconst_le(a->low, a->high, n));
  assert(bvconst_is_normalized(l, n) && bvconst_is_normalized(u, n) && bvconst_le(l, u, n));

  w = a->width;
  assert(w == (n + 31) >> 5);

  if (bvconst_lt(a->low, u, n) && bvconst_le(a->high, l, n)) {
    /*
     * underflow in (a->low - u), no underflow in (a->high - l) 
     * so the enclosing interval is [0b000..., 0b111...]
     */
    bvconst_clear(a->low, w);
    bvconst_set_minus_one(a->high, w);
    bvconst_normalize(a->high, n);
  } else {
    bvconst_sub(a->low, w, u);     // a.low := a.low - u
    bvconst_sub(a->high, w, l);    // a,high := a.high - l
    bvconst_normalize(a->low, n);
    bvconst_normalize(a->high, n);

  }

  assert(bv_interval_is_normalized(a) && bvconst_le(a->low, a->high, n));
}




/*
 * Check for overflow/underflow in a := a0 - b
 * - sa = sign of a0 before the operation
 * - n = number of bits in a and b
 * - overflow: if (a0 >= 0) and (b < 0) and (a < 0)
 * - undeflow: if (a0 < 0) and (b >= 0) and (a >= 0)
 */
static inline bool sub_overflow(uint32_t *a, uint32_t *b, bool sa, uint32_t n) {
  // sign bit of a0 = 0, sign bit of b = 1, sign bit of a = 1
  return !sa & bvconst_tst_bit(b, n-1) & bvconst_tst_bit(a, n-1);
}

static inline bool sub_underflow(uint32_t *a, uint32_t *b, bool sa, uint32_t n) {
  // sign bit of a0 = 1, sign bit of b = 0, sign bit of a = 0
  return sa & !bvconst_tst_bit(b, n-1) & !bvconst_tst_bit(a, n-1);
}


/*
 * Sum of a and [l, n] for signed intervals
 */
static void bv_interval_sub_s_core(bv_interval_t *a, uint32_t *l, uint32_t *u, uint32_t n) {
  uint32_t w;
  bool s_low, s_high;

  assert(n > 0 && n == a->nbits);
  assert(bv_interval_is_normalized(a) && bvconst_sle(a->low, a->high, n));
  assert(bvconst_is_normalized(l, n) && bvconst_is_normalized(u, n) && bvconst_sle(l, u, n));

  w = a->width;
  assert(w == (n + 31) >> 5);

  /*
   * for overflow/underflow detection, store the sign of a->low and a->high
   */
  s_low = bvconst_tst_bit(a->low, n-1);
  s_high = bvconst_tst_bit(a->high, n-1);

  bvconst_sub(a->low, w, u);     // a.low = a.low - u
  bvconst_sub(a->high, w, l);    // a.high = a.high - l
  bvconst_normalize(a->low, n);
  bvconst_normalize(a->high, n);

  if ((sub_underflow(a->low, u, s_low, n) && !sub_underflow(a->high, l, s_high, n)) 
      || (sub_overflow(a->high, l, s_high, n) && !sub_overflow(a->low, u, s_low, n))) {
    bvconst_set_min_signed(a->low, n);
    bvconst_set_max_signed(a->high, n);
  }
  
  assert(bv_interval_is_normalized(a) && bvconst_sle(a->low, a->high, n));
}



void bv_interval_add_u(bv_interval_t *a, bv_interval_t *b) {
  bv_interval_add_u_core(a, b->low, b->high, b->nbits);
}

void bv_interval_add_s(bv_interval_t *a, bv_interval_t *b) {
  bv_interval_add_s_core(a, b->low, b->high, b->nbits);
}


void bv_interval_sub_u(bv_interval_t *a, bv_interval_t *b) {
  bv_interval_sub_u_core(a, b->low, b->high, b->nbits);
}

void bv_interval_sub_s(bv_interval_t *a, bv_interval_t *b) {
  bv_interval_sub_s_core(a, b->low, b->high, b->nbits);
}





/*
 * Overapproximation of [a.low + c * b.low, a.high + c * b.high] modulo 2^n
 * - a and b must have the same bitsize and be normalized
 * - c must be normalized modulo 2^n too
 * - the result is stored in a
 * Unsigned version
 */
void bv_interval_addmul_u(bv_interval_t *a, bv_interval_t *b, uint32_t *c) {
  uint32_t *b_low, *b_high;
  uint32_t n, w;

  b_low = b->low;
  b_high = b->high;
  n = b->nbits;
  w = b->width;

  assert(bvconst_is_normalized(c, n));

  if (bvconst_is_one(c, w)) {
    bv_interval_add_u_core(a, b_low, b_high, n);
  } else if (bvconst_is_minus_one(c, n)) {
    bv_interval_sub_u_core(a, b_low, b_high, n);
  } else {
    // TBD
    bvconst_clear(a->low, w);
    bvconst_set_minus_one(a->high, w);
    bvconst_normalize(a->high, n);
  }
}



/*
 * Overapproximation of [a.low + c * b.low, a.high + c * b.high] modulo 2^n
 * - a and b must have the same bitsize and be normalized
 * - c must be normalized modulo 2^n too
 * - the result is stored in a
 * Signed version
 */
void bv_interval_addmul_s(bv_interval_t *a, bv_interval_t *b, uint32_t *c) {
  uint32_t *b_low, *b_high;
  uint32_t n, w;

  b_low = b->low;
  b_high = b->high;
  n = b->nbits;
  w = b->width;

  assert(bvconst_is_normalized(c, n));

  if (bvconst_is_one(c, w)) {
    bv_interval_add_s_core(a, b_low, b_high, n);
  } else if (bvconst_is_minus_one(c, n)) {
    bv_interval_sub_s_core(a, b_low, b_high, n);
  } else {
    // TBD
    bvconst_set_min_signed(a->low, n);
    bvconst_set_max_signed(a->high, n);
  }
}



