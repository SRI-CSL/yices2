/*
 * The Yices SMT Solver. Copyright 2016 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SLICES IN AN ARRAY OF BITS
 */

#ifndef __BV_SLICES_H
#define __BV_SLICES_H

/*
 * Yices internally represents many bitvector terms as arrays
 * bv[0 ... n-1] where the bv[i] are all Boolean terms.
 *
 * This module recognizes common patterns and attempt to convert
 * bv[0 ... n-1] into a concatenation of slices.
 * Recognized slices include:
 * - [repeat b k]: repeat the same bit k times
 * - [extract u i j]: subvector of u formed by [u[i] ... u[j]]
 * - [constant x k]: constant of k bits (x = its value)
 *
 * The constants 0b00000... and 0b11111... are represented as
 * repeat patterns:
 * - 0b0000... ---> [repeat false_term k] for some k
 * - 0b1111... ---> [repeat true_term k] for some k
 */

#include <stdint.h>
#include <stdbool.h>

#include "terms/terms.h"
#include "utils/int_vectors.h"


/*
 * Each slice is defined by a tag + a descriptor
 */
typedef enum {
  BVSLICE_REPEAT,
  BVSLICE_EXTRACT,
  BVSLICE_CONST64,
  BVSLICE_CONST,
} bvslice_tag_t;

// repeat bit count
typedef struct bvslice_repeat_s {
  term_t bit;
  uint32_t count;
} bvslice_repeat_t;

// vector [low ... high]
typedef struct bvslice_extract_s {
  term_t vector;
  uint32_t low, high;
} bvslice_extract_t;

// [constants of 64bits or less]
typedef struct bvslice_const64_s {
  uint64_t value;
  uint32_t nbits;
} bvslice_const64_t;

// [constants of more than 64 bits]
// value is stored in an array of 32bit words
typedef struct bvslice_const_s {
  uint32_t *value;
  uint32_t nbits;
} bvslice_const_t;

typedef struct bvslice_s {
  bvslice_tag_t tag;
  union {
    bvslice_repeat_t r;
    bvslice_extract_t e;
    bvslice_const64_t c64;
    bvslice_const_t c;
  } desc;
} bvslice_t;


/*
 * Vector to represent a concatenation
 * - also includes an auxiliary vector for intermediate computations
 */
typedef struct bvslicer_s {
  bvslice_t *data;
  uint32_t nelems;
  uint32_t size; // size of the data array
  ivector_t buffer;
} bvslicer_t;

#define DEF_BVSLICER_SIZE 10
#define MAX_BVSLICER_SIZE (UINT32_MAX/sizeof(bvslice_t))



/*
 * Initialize a bvslicer vector
 * - nothing is allocated yet.
 */
extern void init_bvslicer(bvslicer_t *slicer);


/*
 * Reset to the empty vector
 */
extern void reset_bvslicer(bvslicer_t *slicer);


/*
 * Delete: free memory
 */
extern void delete_bvslicer(bvslicer_t *slicer);


/*
 * Process an array of bits a[0 ... n-1]
 * - each element of must be a Boolean term defined in tbl
 * - try to split the array into slices and store the result in slicer
 * - returns true if this succeeds, false otherwise
 */
extern bool slice_bitarray(bvslicer_t *slicer, term_table_t *tbl, const term_t *a, uint32_t n);


/*
 * Check whether slice is of the form [repeat false_term k] or [repeat true_term k]
 * - if so store k in *r
 */
extern bool is_repeat_zero(bvslice_t *d, uint32_t *r);
extern bool is_repeat_one(bvslice_t *d, uint32_t *r);


/*
 * Check for (bv-zero-extend ...) and (bv-sign-extend ...)
 * - d = array of n slices
 * - is_zero_extend(d, n, r) returns true if n>=2 and d[n-1] 
 *   is of the form [repeat false_term k]
 *   it then stores k in *r 
 * - is_sign_extend(tbl, d, n, r) returns true if n>=2 and d[n-1]
 *   if of the form [repeat b k] and d[n-2] is of the form [extract u i j]
 *   and b is equal to (bit u j).
 */
extern bool is_zero_extend(bvslice_t *d, uint32_t n, uint32_t *r);
extern bool is_sign_extend(term_table_t *tbl, bvslice_t *d, uint32_t n, uint32_t *r);


#endif /* __BV_SLICES_H */

