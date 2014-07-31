/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * INTERVALS OF BIT-VECTOR VALUES
 */

/*
 * This is intended for vectors of more than 64bits.
 * For smaller sizes, it's better to use bv64_intervals.
 */

#ifndef __BV_INTERVALS_H
#define __BV_INTERVALS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "terms/bv_constants.h"



/*
 * Interval structure:
 * - low and high are two bitvector constants of n bits (n >= 1)
 * - they are stored as arrays of k 32bit words where k = ceil(n/32)
 * - n is stored in nbits
 * - k is stored in width
 * - the actual size of arrays low and high is stored in size (as a total
 *   number of words)
 * - we always have width <= size
 */
typedef struct bv_interval_s {
  uint32_t *low;
  uint32_t *high;
  uint32_t nbits;
  uint32_t width;
  uint32_t size;
} bv_interval_t;


// default/maximal size
#define BV_INTERVAL_DEF_SIZE 16
#define BV_INTERVAL_MAX_SIZE (UINT32_MAX/32)



/*
 * Auxiliary buffers for addmul
 * - addmul uses auxiliary buffers for internal computation
 * - these buffers are twice as large as the low/high constants
 * - the following structure contains the necessary buffers.
 * - it must be initialized before calling addmul.
 * - addmul will internally reallocate the buffers if they are too small
 */
typedef struct bv_aux_buffers_s {
  uint32_t *buffer_a;
  uint32_t *buffer_b;
  uint32_t *buffer_c;
  uint32_t *buffer_d;
  uint32_t size; // a, b, c, and d all have this size
} bv_aux_buffers_t;



/*
 * AUXILIARY BUFFERS
 */

/*
 * Initialization: nothing is allocated.
 * - all buffers are initialized to NULL
 * - aux->size is 0
 */
extern void init_bv_aux_buffers(bv_aux_buffers_t *aux);


/*
 * Deletion: free memory then reset everything
 */
extern void delete_bv_aux_buffers(bv_aux_buffers_t *aux);




/*
 * INTERVAL OPERATIONS
 */

/*
 * Initialization: don't allocate anything yet.
 * - nbits, width, and size are set to 0
 * - the arrays are allocated on the first call to resize
 */
extern void init_bv_interval(bv_interval_t *intv);


/*
 * Delete: free memory and reset nbits, width, size to 0
 * - intv can be used after delete (it's in the same state as after init).
 */
extern void delete_bv_interval(bv_interval_t *intv);


/*
 * Make sure the arrays low/high are large enough for n bits
 */
extern void resize_bv_interval(bv_interval_t *intv, uint32_t n);


/*
 * Initialize to the point interval [low = x, high = x]
 * - this resizes the arrays if necessary
 * - n must be positive
 * - x must be normalized modulo 2^n (cf. bv_constants.h)
 */
extern void bv_point_interval(bv_interval_t *intv, uint32_t *x, uint32_t n);


/*
 * Initialize to the interval [0, 0]
 * - n must be positive
 * - resize the arrays if necessary
 */
extern void bv_zero_interval(bv_interval_t *intv, uint32_t n);


/*
 * Initialize to the interval [x, y] (unsigned)
 * - n must be positive
 * - x and y must be normalized modulo 2^n
 * - x <= y must hold
 * - the arrays are resized if necessary
 */
extern void bv_interval_set_u(bv_interval_t *intv, uint32_t *x, uint32_t *y, uint32_t n);


/*
 * Initialize to the interval [x, y] (signed)
 * - n must be positive
 * - x and y must be normalized modulo 2^n
 * - x <= y must hold (2s'complement comparison)
 * - the arrays are resized if necessary
 */
extern void bv_interval_set_s(bv_interval_t *intv, uint32_t *x, uint32_t *y, uint32_t n);


/*
 * Initialize to the trivial interval (unsigned)
 * - n must be positive
 * - low is set to 0b000..0
 * - high is set to 0b111..1
 */
extern void bv_triv_interval_u(bv_interval_t *intv, uint32_t n);


/*
 * Initialize to the trivial interval (signed)
 * - n must be positive
 * - low is set to 0b100..0
 * - high is set to 0b0111..1
 */
extern void bv_triv_interval_s(bv_interval_t *intv, uint32_t n);



/*
 * Check whether the two bounds are normalized
 */
static inline bool bv_interval_is_normalized(bv_interval_t *intv) {
  assert(intv->nbits > 0);
  return bvconst_is_normalized(intv->low, intv->nbits) &&
    bvconst_is_normalized(intv->high, intv->nbits);
}


/*
 * Check whether the interval is trivial (contains all possible n-bit vectors)
 */
static inline bool bv_interval_is_triv_u(bv_interval_t *intv) {
  assert(bv_interval_is_normalized(intv));
  return bvconst_is_zero(intv->low, intv->width) &&
    bvconst_is_minus_one(intv->high, intv->nbits);
}

static inline bool bv_interval_is_triv_s(bv_interval_t *intv) {
  assert(bv_interval_is_normalized(intv));
  return bvconst_is_min_signed(intv->low, intv->nbits) &&
    bvconst_is_max_signed(intv->high, intv->nbits);
}


/*
 * Compute the sum of two intervals
 * - a and b must have the same bitsize and be normalized
 * - the result is stored in a
 * Two versions:
 * - add_u: a and b are unsigned intervals
 * - add_s: a and b are signed intervals
 */
extern void bv_interval_add_u(bv_interval_t *a, bv_interval_t *b);
extern void bv_interval_add_s(bv_interval_t *a, bv_interval_t *b);


/*
 * Compute a - b: store the result in a
 * - a and b must have the same bitsize and be normalized
 * Two versions:
 * - add_u: a and b are unsigned intervals
 * - add_s: a and b are signed intervals
 */
extern void bv_interval_sub_u(bv_interval_t *a, bv_interval_t *b);
extern void bv_interval_sub_s(bv_interval_t *a, bv_interval_t *b);


/*
 * Approximation of the interval a + c * b
 * - a and b must have the same bitsize and be normalized
 * - c must be normalized modulo 2^n (where n = size of a and b)
 * - the result is stored in a
 *
 * The result is precise only if the constant c and the intervals a and b
 * are small.
 * - in the unsigned version: a, b are unsigned, c is interpreted as
 *   an unsigned integer (between 0 and 2^n-1)
 * - in the signed version: a, b are signed intervals, and c is interpreted
 *   as a 2's complement, signed integer.
 *
 * The extra argument aux must be an initialized aux_buffer structure. It's used for internal
 * computations if needed.
 */
extern void bv_interval_addmul_u(bv_interval_t *a, bv_interval_t *b, uint32_t *c, bv_aux_buffers_t *aux);
extern void bv_interval_addmul_s(bv_interval_t *a, bv_interval_t *b, uint32_t *c, bv_aux_buffers_t *aux);



#endif /* __BV_INTERVALS_H */
