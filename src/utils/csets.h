/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SETS OF INTEGERS IN A RANGE [0... n-1]
 */

#ifndef __CSETS_H
#define __CSETS_H


#include <stdint.h>
#include <stdbool.h>

#include "utils/int_vectors.h"


/*
 * Data structure
 * - dsize = size of the domain
 * - elements are in the interval [0 ... dsize - 1]
 * - data = array of w words where w = ceil(dsize/32)
 *   data is used as a bitvector: if i is in the set
 *   and i = 32k + r (with 0 <= r < 31) then
 *   bit r in data[k] i set to 1
 *
 * - in addition, we store a 32bit hash: bit[i] of hash is 1
 *   if there's an element of index (i + 32k) in the set
 *
 * Optimization: if dsize <= 32, hash is enough. We don't allocate
 * a bitvector at all.
 *
 * On initialization and after reset, dsize is set to 0.
 */
typedef struct cset_s {
  uint32_t dsize;
  uint32_t hash;
  uint32_t *data;
} cset_t;



/*
 * Initialize
 */
extern void init_cset(cset_t *s);

/*
 * Delete: free the data array if non-NULL
 */
extern void delete_cset(cset_t *s);

/*
 * Reset: delete data if non-NULL, reset dsize to 0
 */
extern void reset_cset(cset_t *s);


/*
 * Set the domain size to n
 * - s->dzize must be 0 (i.e., just after reset or init)
 * - n must be positive
 * - s is set to the empty or full set
 */
extern void cset_init_empty(cset_t *s, uint32_t n);
extern void cset_init_full(cset_t *s, uint32_t n);


/*
 * Check emptiness
 */
static inline bool cset_is_empty(cset_t *s) {
  return s->hash == 0;
}


/*
 * Number of elements in s
 */
extern uint32_t cset_card(cset_t *s);


/*
 * Check membership
 * - i must satisfy 0 <= i < s->dsize
 */
extern bool cset_member(cset_t *s, uint32_t i);


/*
 * Checks: s1 and s2 must have the same domain
 * (equal and positive dsize)
 * - cset_subset(s1, s2): true means s1 is a subset of s2
 * - cset_disjoint(s1, s2): true means s1 and s2 are disjoint
 */
extern bool cset_subset(cset_t *s1, cset_t *s2);
extern bool cset_disjoint(cset_t *s1, cset_t *s2);


/*
 * Add/remove elements
 * - cset_empty(s): remove all elements of s
 * - cset_fill(s):  add the full domain to s
 *
 * - cset_add(s, i): add element i
 * - cset_remove(s, i): remove i
 *   (i must satisfy 0 <= i < s->dsize)
 *
 * - cset_add_set(s, s1): add all elements of s1 to s
 * - cset_remove_set(s, s1): remove all elements of s1 from s
 *   (s1 must have the same domain as s2)
 *
 * - cset_add_array(s, a, n): add all elements of a
 * - cset_remove_array(s, a, n): remove all elements of a from s
 *   (each element of a must be in [0, s->dsize-1])
 */
extern void cset_empty(cset_t *s);
extern void cset_fill(cset_t *s);
extern void cset_add(cset_t *s, uint32_t i);
extern void cset_remove(cset_t *s, uint32_t i);
extern void cset_add_set(cset_t *s, cset_t *s1);
extern void cset_remove_set(cset_t *s, cset_t *s1);
extern void cset_add_array(cset_t *s, uint32_t *a, uint32_t n);
extern void cset_remove_array(cset_t *s, uint32_t *a, uint32_t n);



/*
 * Copy the elements of s into vector v
 * - v is not reset: elements are added at the end of v
 */
extern void cset_extract(cset_t *s, ivector_t *v);


#endif /* __CSETS_H */

