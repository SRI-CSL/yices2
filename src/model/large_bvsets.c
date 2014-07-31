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

#include "utils/memalloc.h"
#include "utils/hash_functions.h"
#include "utils/prng.h"
#include "model/large_bvsets.h"

/*
 * Initialize a large set for bitsize n
 * - k = bitsize of internal vector
 * - use the default size for s->set
 * - allocate fresh_val vector of default size
 */
void init_large_bvset(large_bvset_t *s, uint32_t n, uint32_t k) {
  assert(k < 32);

  if (k == 0) {
    k = BVSET_DEF_SIZE;
  } else {
    k = ((uint32_t) 1) << k; // 2^k
  }

  s->set = allocate_bitvector0(k);
  s->size = k;
  s->nelems = 0;
  s->max_val = UINT32_MAX;
  if (n < 32) {
    s->max_val = (((uint32_t) 1) << n) - 1; // 2^n - 1
  }

  k = BVSET_DEF_FSIZE;
  assert(k < BVSET_MAX_FSIZE);
  s->fresh_vals = (uint32_t *) safe_malloc(k * sizeof(uint32_t));
  s->fsize = k;
  s->nfresh = 0;
}


/*
 * Delete s
 */
void delete_large_bvset(large_bvset_t *s) {
  delete_bitvector(s->set);
  safe_free(s->fresh_vals);
  s->set = NULL;
  s->fresh_vals = NULL;
}


/*
 * Empty s and restore the default size
 */
void reset_large_bvset(large_bvset_t *s) {
  uint32_t n;

  n = s->size;
  clear_bitvector(s->set, n);
  s->nelems = 0;
  s->nfresh = 0;
}


/*
 * Extend the fresh_vals array by 50%
 */
static void extend_large_bvset_fvals(large_bvset_t *s) {
  uint32_t n;

  n = s->fsize + 1;
  n += n>>1;

  if (n >= BVSET_MAX_FSIZE) {
    out_of_memory();
  }

  s->fresh_vals = (uint32_t *) safe_realloc(s->fresh_vals, n * sizeof(uint32_t));
  s->fsize = n;
}



/*
 * Store x in s's fresh_vals array
 */
static void large_bvset_store_fval(large_bvset_t *s, uint32_t x) {
  uint32_t i;

  i = s->nfresh;
  if (i == s->fsize) {
    extend_large_bvset_fvals(s);
  }
  assert(i < s->fsize);
  s->fresh_vals[i] = x;
  s->nfresh = i+1;
}


/*
 * Add value x to set s
 */
void large_bvset_add(large_bvset_t *s, uint32_t x) {
  uint32_t i, mask;

  assert(x <= s->max_val);

  mask = s->size - 1;
  i = jenkins_hash_uint32(x) & mask;
  assert(i < s->size);

  if (! tst_bit(s->set, i)) {
    set_bit(s->set, i);
    s->nelems ++;
  }
}


/*
 * Check whether x is absent
 * - true means hash(x) is not in S so x is absent
 * - false means hash(x) is in S so either x or some y
 *   with the same hash code is present.
 */
bool large_bvset_test_absent(large_bvset_t *s, uint32_t x) {
  uint32_t i, mask;

  assert(x <= s->max_val);
  mask = s->size - 1;
  i = jenkins_hash_uint32(x) & mask;
  assert(i < s->size);
  return ! tst_bit(s->set, i);
}


/*
 * Search for a non-zero fresh value in interval [t, t+n]
 * - return 0 if nothing is found
 * - return the fresh value and add it to s otherwise
 */
static uint32_t large_bvset_search_fresh(large_bvset_t *s, uint32_t t, uint32_t n) {
  uint32_t i, mask;

  assert(t <= s->max_val);

  mask = s->size - 1;
  while (n > 0) {
    if (t != 0) {
      // check whether t is used
      i = jenkins_hash_uint32(t) & mask;
      assert(i < s->size);
      if (! tst_bit(s->set, i)) {
        // t is fresh, i = hash code for t
        set_bit(s->set, i);
        s->nelems ++;
        large_bvset_store_fval(s, t);
        return t;
      }
      n --;
    }
    t ++;
    t &= s->max_val;
  }

  return 0;
}


/*
 * Attempt to find a non-zero value x not in s, then add it to s.
 * - return 0 if this fails
 * - return x otherwise
 * - the fresh value is copied into s's internal fresh_val vector
 */
uint32_t large_bvset_get_fresh(large_bvset_t *s) {
  uint32_t n, t, x;

  n = BVSET_NUM_TRIES;
  assert(n > 0);
  do {
    t = random_uint32() & s->max_val;
    x = large_bvset_search_fresh(s, t, BVSET_DELTA);
    if (x != 0) break;
    n --;
  } while (n > 0);

  return x;
}

