/*
 * Sets of unsigned integers represented as bitvectors
 */

#ifndef __INT_BV_SETS_H
#define __INT_BV_SETS_H

#include <stdint.h>
#include <stdbool.h>

#include "bitvectors.h"


/*
 * Structure:
 * - data = bitvector 
 * - size = number of bits in mask
 * - nbits = number of meaningful bits (i.e. initialized)
 */
typedef struct int_bvset_s {
  byte_t *data;
  uint32_t size;
  uint32_t nbits;
} int_bvset_t;


// default and maximal size
#define DEF_INT_BVSET_SIZE 1024
#define MAX_INT_BVSET_SIZE UINT32_MAX


/*
 * Initialize set:
 * - n = initial size. If n == 0, the default size is used.
 * - the set is initially empty
 */
extern void init_int_bvset(int_bvset_t *set, uint32_t n);


/*
 * Delete set: release memory
 */
extern void delete_int_bvset(int_bvset_t *set);


#if 0
/*
 * Increase size and nbits, make data large enough for adding element x
 * - requires x >= set->nbits
 */
extern void resize_int_bvset(int_bvset_t *set, uint32_t x);
#endif


/*
 * Empty the set
 */
static inline void reset_int_bvset(int_bvset_t *set) {
  set->nbits = 0;
}


/*
 * Check whether the set is empty (has been reset)
 */
static inline bool int_bvset_is_empty(int_bvset_t *set) {
  return set->nbits == 0;
}


/*
 * Check whether x belongs to set
 * - x must be non-negative
 */
static inline bool int_bvset_member(int_bvset_t *set, uint32_t x) {
  return x < set->nbits && tst_bit(set->data, x);
}


/*
 * Add x to the set
 * - x must be non-negative
 * - return true if x not already present
 * - return false if x is present
 */
extern bool int_bvset_add(int_bvset_t *set, uint32_t x);


#endif /* __INT_BV_SETS_H */
