/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SETS OF BIT-VECTOR VALUES: APPROXIMATE REPRESENTATION (BLOOM-FILTER)
 *
 * This is used in model construction when fresh-values of type (bitvector n)
 * are requested.
 * - each set is initialized for a fixed bit size n
 * - each element is stored as an unsigned 32bit integer,
 *   with high-order bits 0 if n < 32.
 * - if n > 32, then some conversion must be used to convert values
 *   stored (32 bits) to the desired size (n bits) by padding.
 * This is enough since we want to search for elements not in the set,
 * so picking from a subdomain of 2^32 values should be plenty.
 *
 * We map the full domain (2^32) to a smaller set S of size 2^k for
 * a small k (default k = 13) using a hash function. To generate
 * fresh values we search for x in [0 ... 2^n-1] such that hash(x)
 * is not in S.
 *
 * WARNING: because of collisions in hash, we can fail to find
 * such x even if S is not full.
 */

#ifndef __LARGE_BVSETS_H
#define __LARGE_BVSETS_H

#include <stdint.h>
#include <stdbool.h>

#include "utils/bitvectors.h"


/*
 * Data-structures:
 * - set = bitvector of 2^k bits for some k <= n
 * - size = 2^k
 * - nelems = number of bits set in set = card of S
 * - max_val = max value in the domain:
 *   if n <= 31 then max_val = 2^n-1,
 *   if n >= 32, max_val = UINT32_MAX = 2^32-1
 *   valid values are in the interval [0 ... max_val]
 * - fresh_vals = array where we store the fresh values
 * - fsize = size of that array
 * - nfresh = number of elements in fresh_vals
 *
 * All values are represented as 32bit unsigned integers. For bitvectors
 * of size n > 32, some convention must be used to convert to and from
 * 32bit unsigned integers and bitvectors of size n.
 *
 * The algorithm to find fresh values is parameterized by DELTA
 * and NUM_TRIES:
 * - pick a random t between 0 and s->max_val
 * - search for an unmarked x in [t, t+DELTA]. If that fails, try another t.
 *   NUM_TRIES = max number of tries.
 * - x=0 is used to report failure so fresh values are always non null.
 */
typedef struct large_bvset_s {
  byte_t *set;
  uint32_t size;
  uint32_t nelems;
  uint32_t max_val;
  uint32_t *fresh_vals;
  uint32_t fsize;
  uint32_t nfresh;
} large_bvset_t;


/*
 * Default and max sizes
 */
#define BVSET_DEF_SIZE 8192
#define BVSET_DEF_FSIZE 10
#define BVSET_MAX_FSIZE (UINT32_MAX/sizeof(uint32_t))

/*
 * Search parameters
 */
#define BVSET_DELTA 15
#define BVSET_NUM_TRIES 6


/*
 * Initialize a large set for bitsize n, mapped to size 2^k
 * - if k = 0, we use the default size for s->set
 * - k must be at most 31
 * - allocate a fresh_val vector of default size too
 */
extern void init_large_bvset(large_bvset_t *s, uint32_t n, uint32_t k);

/*
 * Delete: free memory
 */
extern void delete_large_bvset(large_bvset_t *s);

/*
 * Reset: empty the set
 */
extern void reset_large_bvset(large_bvset_t *s);

/*
 * Add value x to the set
 * - x must be in the interval [0 .. s->max_val]
 */
extern void large_bvset_add(large_bvset_t *s, uint32_t x);

/*
 * Check whether x is absent
 * - true means hash(x) is not in S so x is absent
 * - false means hash(x) is in S so either x or some y
 *   with the same hash code is present.
 */
extern bool large_bvset_test_absent(large_bvset_t *s, uint32_t x);

/*
 * Attempt to find a non-zero value x not in s, then add it to s.
 * - return 0 if this fails
 * - return x otherwise
 */
extern uint32_t large_bvset_get_fresh(large_bvset_t *s);



#endif /* __LATGE_BVSETS_H */
