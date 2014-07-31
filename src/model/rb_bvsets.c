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

#include "model/rb_bvsets.h"

/*
 * Initialize set for bitsize n
 * - n must be positive
 */
void init_rb_bvset(rb_bvset_t *set, uint32_t n) {
  assert(n > 0);

  init_rbtree(&set->tree, 0);
  set->max_val = UINT32_MAX;
  if (n < 32) {
    set->max_val = (((uint32_t) 1) << n) - 1; // 2^n - 1
  }
  set->ptr = 0;
}


/*
 * Check whether set is full: all elements in [0 ... max_val]
 * are present in the set.
 * - we use the fact that the number of nodes in a tree is
 *   less than MAX_RBTREE_SIZE, which is less than 2^32.
 */
bool rb_bvset_full(rb_bvset_t *set) {
  return (set->max_val < UINT32_MAX) && (rbtree_card(&set->tree) == set->max_val + 1);
}



/*
 * Return a fresh x not in the set then add x to set
 * - the set must not be full
 */
uint32_t rb_bvset_get_fresh(rb_bvset_t *set) {
  uint32_t x;

  assert(! rb_bvset_full(set));

  /*
   * Naive technique: scan from 0 to .. max_val
   * (todo: use a random search first, then revert
   * to the naive method)??
   */
  x = set->ptr;
  while (rbtree_is_present(&set->tree, x)) {
    x ++;
  }
  assert(x <= set->max_val);
  rbtree_add(&set->tree, x);
  set->ptr = x+1;

  return x;
}
