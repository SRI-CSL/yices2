/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SUPPORT FOR CONSTRUCTING FRESH BIT-VECTOR VALUES
 * AND MAINTAINING SETS OF USED VALUES
 *
 * This is used in model construction when fresh-values of type (bitvector n)
 * are requested.
 */

#include <assert.h>

#include "model/small_bvsets.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"
#include "utils/prng.h"


/*
 * Initialize a small set for bitsize n
 * - n must be positive and no more than 31
 */
void init_small_bvset(small_bvset_t *s, uint32_t n) {
  uint32_t size;

  assert(0 < n && n < 32);
  size = (1 << n);
  s->set = allocate_bitvector0(size);
  s->size = size;
  s->nelems = 0;
  s->ptr = 0;
}

/*
 * Delete s: free memory
 */
void delete_small_bvset(small_bvset_t *s) {
  delete_bitvector(s->set);
  s->set = NULL;
}

/*
 * Reset s: empty it
 */
void reset_small_bvset(small_bvset_t *s) {
  clear_bitvector(s->set, s->size);
  s->nelems = 0;
  s->ptr = 0;
}


/*
 * Add element x to s
 * - x must be between 0 and 2^n where n = bitsize of s
 */
void small_bvset_add(small_bvset_t *s, uint32_t x) {
  assert(x < s->size);

  if (! tst_bit(s->set, x)) {
    set_bit(s->set, x);
    s->nelems ++;
  }
}


/*
 * Create a fresh value and return it
 * - s must not be full
 * - return an x that's not yet in the set s
 */
uint32_t small_bvset_get_fresh(small_bvset_t *s) {
  uint32_t i;

  assert(s->nelems < s->size);

  i = s->ptr;
  assert(i < s->size);
  while (tst_bit(s->set, i)) {
    i ++;
    assert(i < s->size);
  }

  s->ptr = i;
  s->nelems ++;
  set_bit(s->set, i);

  return i;
}

