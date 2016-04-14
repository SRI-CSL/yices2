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
 */

#include <stdint.h>
#include <stdbool.h>

#include "terms/terms.h"


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

// [vector [left ... right]]
typedef struct bvslice_extract_s {
  term_t vector;
  uint32_t left, right;
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
 */
typedef struct bvslicer_s {
  bvslice_t *data;
  uint32_t nelems;
  uint32_t size; // size of the data array
} bvslicer_t;

#define DEF_BVSLICER_SIZE 4
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
 * - try to split it into slices and store the result in slicer
 * - returns true if this succeeds, false otherwise
 * - if the function returns false, the slicer is returned empty.
 */
extern bool slice_bitarray(bvslicer_t *slicer, term_table_t *tbl, const term_t *a, uint32_t n);


#endif /* __BV_SLICES_H */

