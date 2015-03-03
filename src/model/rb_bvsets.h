/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SETS OF BIT-VECTOR VALUES REPRESENTED AS RED-BLACK TREES
 *
 * This is used in model construction when fresh-values of type
 * (bitvector n) are requested.
 * - each set is initialized for a fixed bit size n
 * - each element is stored as an unsigned 32bit integer,
 *   with high-order bits 0 if n < 32.
 * - if n > 32, then some conversion must be used to convert values
 *   stored (32 bits) to the desired size (n bits) by padding.
 * This is enough since we want to search for elements not in the set,
 * so picking from a subdomain of 2^32 values should be plenty.
 *
 */

#ifndef __RB_BVSETS_H
#define __RB_BVSETS_H

#include <stdint.h>
#include <stdbool.h>

#include "utils/uint_rbtrees.h"

/*
 * Data structure for a set of n-bit vectors:
 * - tree: red-black tree that stores the actual values
 * - max_var = 2^n-1 if n <= 32, UINT32_MAX = 2^321 otherwise
 * - ptr = an element in [0 ... max_var] used to scan the tree
 *   (for generating fresh values)
 */
typedef struct rb_bvset_s {
  rbtree_t tree;
  uint32_t max_val;
  uint32_t ptr;
} rb_bvset_t;



/*
 * Initialize set for bitsize n
 * - n must be positive
 */
extern void init_rb_bvset(rb_bvset_t *set, uint32_t n);


/*
 * Delete: free memory
 */
static inline void delete_rb_bvset(rb_bvset_t *set) {
  delete_rbtree(&set->tree);
}


/*
 * Reset: empty the set
 */
static inline void reset_rb_bvset(rb_bvset_t *set) {
  reset_rbtree(&set->tree);
  set->ptr = 0;
}


/*
 * Add x to the set
 * - x must be in the interval [0 ... set->max_val]
 */
static inline void rb_bvset_add(rb_bvset_t *set, uint32_t x) {
  assert(x <= set->max_val);
  rbtree_add(&set->tree, x);
}


/*
 * Check whether x is present in set
 * - x must be in the interval [0 ... set->max_val]
 */
static inline bool rb_bvset_member(rb_bvset_t *set, uint32_t x) {
  assert(x <= set->max_val);
  return rbtree_is_present(&set->tree, x);
}


/*
 * Check whether the set is full (i.e., all elements in [0 ... set->max_val]
 * are stored in the set.
 * - we can't have more than MAX_RBTREE_SIZE nodes in red-black trees.
 * - so full sets are possible only if max_val < MAX_RBTREE_SIZE,
 *   i.e., bitsize is 28 or less.
 * - we'll run out of memory long before we have trees of 2^28 nodes
 *   so that's no big deal.
 */
extern bool rb_bvset_full(rb_bvset_t *set);


/*
 * Get a fresh x not in set then add it to set
 * - the set must not be full
 * - return x.
 */
extern uint32_t rb_bvset_get_fresh(rb_bvset_t *set);



#endif /* __RB_BVSETS_H */
