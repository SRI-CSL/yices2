/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * INTERVALS OF BIT-VECTOR VALUES
 */

#include "solvers/bv/bv_intervals.h"
#include "utils/memalloc.h"

/*
 * AUXILIARY BUFFERS
 */

/*
 * Initialization: nothing is allocated.
 * - all buffers are initialized to NULL
 * - aux->size is 0
 */
void init_bv_aux_buffers(bv_aux_buffers_t *aux) {
  aux->buffer_a = NULL;
  aux->buffer_b = NULL;
  aux->buffer_c = NULL;
  aux->buffer_d = NULL;
  aux->size = 0;
}


/*
 * Deletion: free memory
 */
void delete_bv_aux_buffers(bv_aux_buffers_t *aux) {
  safe_free(aux->buffer_a);
  safe_free(aux->buffer_b);
  safe_free(aux->buffer_c);
  safe_free(aux->buffer_d);
  aux->buffer_a = NULL;
  aux->buffer_b = NULL;
  aux->buffer_c = NULL;
  aux->buffer_d = NULL;
  aux->size = 0;
}


/*
 * Resize: make sure all buffers are large enough
 * for at least n words
 */
static void bv_aux_buffers_set_size(bv_aux_buffers_t *aux, uint32_t n) {
  if (aux->size < n) {
    if (n < BV_INTERVAL_DEF_SIZE) {
      n = BV_INTERVAL_DEF_SIZE;
    }
    assert(n <= BV_INTERVAL_MAX_SIZE);
    aux->buffer_a = (uint32_t *) safe_realloc(aux->buffer_a, n * sizeof(uint32_t));
    aux->buffer_b = (uint32_t *) safe_realloc(aux->buffer_b, n * sizeof(uint32_t));
    aux->buffer_c = (uint32_t *) safe_realloc(aux->buffer_c, n * sizeof(uint32_t));
    aux->buffer_d = (uint32_t *) safe_realloc(aux->buffer_d, n * sizeof(uint32_t));
    aux->size = n;
  }
}



/*
 * Compute a + b * c using aux
 * - a, b, and c must all be normalized modulo 2^n
 * - a, b, and c are interpreted as unsigned integers
 * - aux->size must be large enough to store bitvectors of size 2*n
 * - the result is stored in aux->buffer_a as a bitvector of size 2*n
 * - side effect: use buffer_c and buffer_d
 */
static void bv_aux_addmul_u(bv_aux_buffers_t *aux, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t n) {
  uint32_t n2, w;

  n2 = n + n;
  w = (n2 + 31) >> 5;
  assert(aux->size >= w);

  bvconst_set_extend(aux->buffer_a, n2, a, n, 0); // buffer_a := zero_extend a to size 2n
  bvconst_set_extend(aux->buffer_c, n2, b, n, 0); // buffer_c := zero_extend b
  bvconst_set_extend(aux->buffer_d, n2, c, n, 0); // buffer_d := zero_extend c

  bvconst_addmul(aux->buffer_a, w, aux->buffer_c, aux->buffer_d); // buffer_a := buffer_a + buffer_c * buffer_d
  bvconst_normalize(aux->buffer_a, n2);
}



/*
 * Same thing for a - b * c
 */
static void bv_aux_submul_u(bv_aux_buffers_t *aux, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t n) {
  uint32_t n2, w;

  n2 = n + n;
  w = (n2 + 31) >> 5;
  assert(aux->size >= w);

  bvconst_set_extend(aux->buffer_a, n2, a, n, 0); // buffer_a := zero_extend a to size 2n
  bvconst_set_extend(aux->buffer_c, n2, b, n, 0); // buffer_c := zero_extend b
  bvconst_set_extend(aux->buffer_d, n2, c, n, 0); // buffer_d := zero_extend c

  bvconst_submul(aux->buffer_a, w, aux->buffer_c, aux->buffer_d); // buffer_a := buffer_a + buffer_c * buffer_d
  bvconst_normalize(aux->buffer_a, n2);
}


/*
 * Same thing for a + b * c, this time interpreted as signed integers
 */
static void bv_aux_addmul_s(bv_aux_buffers_t *aux, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t n) {
  uint32_t n2, w;

  n2 = n + n;
  w = (n2 + 31) >> 5;
  assert(aux->size >= w);

  bvconst_set_extend(aux->buffer_a, n2, a, n, -1); // buffer_a := sign_extend a to size 2n
  bvconst_set_extend(aux->buffer_c, n2, b, n, -1); // buffer_c := sign_extend b
  bvconst_set_extend(aux->buffer_d, n2, c, n, -1); // buffer_d := sign_extend c

  bvconst_addmul(aux->buffer_a, w, aux->buffer_c, aux->buffer_d); // buffer_a := buffer_a + buffer_c * buffer_d
  bvconst_normalize(aux->buffer_a, n2);
}


/*
 * Swap buffer_a and buffer_b
 */
static inline void bv_aux_swap_ab(bv_aux_buffers_t *aux) {
  uint32_t *tmp;

  tmp = aux->buffer_a;
  aux->buffer_a = aux->buffer_b;
  aux->buffer_b = tmp;
}


/*
 * Shift buffer_a right by n bits and store the result in buffer_c
 * then normalize buffer_a modulo 2^n.
 * This stores the quotient of buffer_a by 2^n in buffer_c
 * and the remainder of buffer_a divided by 2^n in buffer_a.
 */
static inline void bv_aux_shift_a_to_c(bv_aux_buffers_t *aux, uint32_t n) {
  uint32_t n2;
  uint32_t w;

  n2 = n + n;
  w = (n2 + 31) >> 5;
  assert(aux->size >= w);
  bvconst_set(aux->buffer_c, w, aux->buffer_a);  // buffer_c := buffer_a
  bvconst_shift_right(aux->buffer_c, n2, n, 0);  // buffer_c := quotient
  bvconst_normalize(aux->buffer_a, n);           // buffer_a := remainder
}

/*
 * Shift buffer_b right by n bits and store the result in buffer_d
 * then normalize buffer_b modulo 2^n.
 * This stores the quotient of buffer_b by 2^n in buffer_d
 * and the remainder of buffer_b divided by 2^n in buffer_b.
 */
static inline void bv_aux_shift_b_to_d(bv_aux_buffers_t *aux, uint32_t n) {
  uint32_t n2;
  uint32_t w;

  n2 = n + n;
  w = (n2 + 31) >> 5;
  assert(aux->size >= w);
  bvconst_set(aux->buffer_d, w, aux->buffer_b);  // buffer_d := buffer_b
  bvconst_shift_right(aux->buffer_d, n2, n, 0);  // buffer_d := quotient
  bvconst_normalize(aux->buffer_b, n);           // buffer_b := remainder
}


/*
 * INTERVALS
 */

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

  if (bvconst_lt(a->high, u, n) && bvconst_ge(a->low, l, n)) {
    /*
     * Overflow in a->high, no overflow in a->low so we have
     * (a->low + l) < 2^n <= (a->high + u).
     * The enclosing interval is [0b000..., 0b111...]
     */
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
 * - underflow: if (a0 < 0) and (b < 0) and (a >= 0)
 */
static inline bool add_overflow(uint32_t *a, uint32_t *b, bool sa, uint32_t n) {
  // sign bit of a0 = 0, sign bit of b = 0, sign bit of a = 1
  return !sa && !bvconst_tst_bit(b, n-1) && bvconst_tst_bit(a, n-1);
}

static inline bool add_underflow(uint32_t *a, uint32_t *b, bool sa, uint32_t n) {
  // sign bit of a0 = 1, sign bit of b = 1, sign bit of a = 0
  return sa && bvconst_tst_bit(b, n-1) && !bvconst_tst_bit(a, n-1);
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

  if (bvconst_lt(a->low, u, n) && bvconst_ge(a->high, l, n)) {
    /*
     * (a->low - u) will underflow
     * (a->high - l) will not underflow
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
 * - underflow: if (a0 < 0) and (b >= 0) and (a >= 0)
 */
static inline bool sub_overflow(uint32_t *a, uint32_t *b, bool sa, uint32_t n) {
  // sign bit of a0 = 0, sign bit of b = 1, sign bit of a = 1
  return !sa && bvconst_tst_bit(b, n-1) && bvconst_tst_bit(a, n-1);
}

static inline bool sub_underflow(uint32_t *a, uint32_t *b, bool sa, uint32_t n) {
  // sign bit of a0 = 1, sign bit of b = 0, sign bit of a = 0
  return sa && !bvconst_tst_bit(b, n-1) && !bvconst_tst_bit(a, n-1);
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
 *
 * The extra argument aux must be an initialized aux_buffer structure. It's used for internal
 * computations if needed.
 */
void bv_interval_addmul_u(bv_interval_t *a, bv_interval_t *b, uint32_t *c, bv_aux_buffers_t *aux) {
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
    bv_aux_buffers_set_size(aux, 2 * w); // make the buffers large enough

    if (!bvconst_tst_bit(c, n-1)) {
      // c is less than 2^(n-1)
      bv_aux_addmul_u(aux, a->high, b_high, c, n);
      bv_aux_swap_ab(aux);
      bv_aux_addmul_u(aux, a->low, b_low, c, n);
      bv_aux_shift_a_to_c(aux, n);
      bv_aux_shift_b_to_d(aux, n);

      /*
       * Let L = a->low + c * b->low and H = a->high + c * b->high.
       * At this point we have:
       * - remainder of L/2^n in aux->buffer_a
       * - remainder of H/2^n in aux->buffer_b
       * - quotient of L/2^n  in aux->buffer_c
       * - quotient of H/2^n  in aux->buffer_d
       *
       * If the two quotients are equal, then we can use the
       * two remainders as bounds. Otherwise, we return the
       * trivial interval.
       */
      if (bvconst_eq(aux->buffer_c, aux->buffer_d, w)) {
        bvconst_set(a->low, w, aux->buffer_a);
        bvconst_set(a->high, w, aux->buffer_b);
      } else {
        bvconst_clear(a->low, w);
        bvconst_set_minus_one(a->high, w);
        bvconst_normalize(a->high, n);
      }

    } else {
      // c is more than 2^(n-1), we use c' = -c modulo 2^n
      bvconst_negate(c, w);
      bvconst_normalize(c, n);

      bv_aux_submul_u(aux, a->high, b_low, c, n);
      bv_aux_swap_ab(aux);
      bv_aux_submul_u(aux, a->low, b_high, c, n);
      bv_aux_shift_a_to_c(aux, n);
      bv_aux_shift_b_to_d(aux, n);

      /*
       * Let L = a->low - c' * b->high and H = a->high - c' * b->low.
       * At this point we have:
       * - remainder of L/2^n in aux->buffer_a
       * - remainder of H/2^n in aux->buffer_b
       * - quotient of L/2^n  in aux->buffer_c
       * - quotient of H/2^n  in aux->buffer_d
       */
      if (bvconst_eq(aux->buffer_c, aux->buffer_d, w)) {
        bvconst_set(a->low, w, aux->buffer_a);
        bvconst_set(a->high, w, aux->buffer_b);
      } else {
        bvconst_clear(a->low, w);
        bvconst_set_minus_one(a->high, w);
        bvconst_normalize(a->high, n);
      }

      // restore c's value
      bvconst_negate(c, w);
      bvconst_normalize(c, n);
    }

    assert(bv_interval_is_normalized(a) && bvconst_le(a->low, a->high, n));
  }
}



/*
 * Overapproximation of [a.low + c * b.low, a.high + c * b.high] modulo 2^n
 * - a and b must have the same bitsize and be normalized
 * - c must be normalized modulo 2^n too
 * - the result is stored in a
 * Signed version.
 *
 * The extra argument aux must be an initialized aux_buffer structure. It's used for internal
 * computations if needed.
 */
void bv_interval_addmul_s(bv_interval_t *a, bv_interval_t *b, uint32_t *c, bv_aux_buffers_t *aux) {
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
    bv_aux_buffers_set_size(aux, 2 * w); // make the buffers large enough

    if (!bvconst_tst_bit(c, n-1)) {
      // c is non-negative
      bv_aux_addmul_s(aux, a->high, b_high, c, n);
      bv_aux_swap_ab(aux);
      bv_aux_addmul_s(aux, a->low, b_low, c, n);
      bv_aux_shift_a_to_c(aux, n);
      bv_aux_shift_b_to_d(aux, n);

      /*
       * Here we have:
       * remainder of (a->low + c * b->low) divided by 2^n in buffer_a
       * remainder of (a->high + c * b->high) divided by 2^n in buffer_b
       * quotient of (a->low + c * b->low) divided by 2^n in buffer_c
       * quotient of (a->high + c * b->high) divided by 2^n in buffer_d
       */
    } else {
      // c is negative
      bv_aux_addmul_s(aux, a->high, b_low, c, n);
      bv_aux_swap_ab(aux);
      bv_aux_addmul_s(aux, a->low, b_high, c, n);
      bv_aux_shift_a_to_c(aux, n);
      bv_aux_shift_b_to_d(aux, n);

      /*
       * Here we have:
       * remainder of (a->low + c * b->low) divided by 2^n in buffer_a
       * remainder of (a->high + c * b->high) divided by 2^n in buffer_b
       * quotient of (a->low + c * b->low) divided by 2^n in buffer_c
       * quotient of (a->high + c * b->high) divided by 2^n in buffer_d
       */
    }

    if (bvconst_eq(aux->buffer_c, aux->buffer_d, w) && bvconst_sle(aux->buffer_a, aux->buffer_b, n)) {
      // equal quotients and buffer_a <= buffer_b
      bvconst_set(a->low, w, aux->buffer_a);
      bvconst_set(a->high, w, aux->buffer_b);
    } else {
      bvconst_add_one(aux->buffer_c, w);
      if (bvconst_eq(aux->buffer_c, aux->buffer_d, w) &&
          bvconst_tst_bit(aux->buffer_a, n-1)  && !bvconst_tst_bit(aux->buffer_b, n-1)) {
        // quotient for low = quotient for high -1
        // remainder for low is negative
        // remainder for high is positive
        bvconst_set(a->low, w, aux->buffer_a);
        bvconst_set(a->high, w, aux->buffer_b);
      } else {
        // the full interval is larger than 2^n
        bvconst_set_min_signed(a->low, n);
        bvconst_set_max_signed(a->high, n);
      }
    }
  }
}



