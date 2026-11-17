/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * STORE OF HASH-CONS'ED SETS/ARRAYS OF INTEGERS
 */

#ifndef __INT_HARRAY_STORE_H
#define __INT_HARRAY_STORE_H

#include <stddef.h>
#include <stdint.h>

#include "utils/int_array_hsets.h"
#include "utils/int_hash_sets.h"
#include "utils/int_vectors.h"

/*
 * Store: 
 * - hash-set for arrays themselves
 * - all arrays stored in hset are sorted in increasing order
 * - aux & buffer are used internally for computing unions
 */
typedef struct int_harray_store_s {
  int_array_hset_t hset;
  ivector_t buffer;
  int_hset_t aux;
} int_harray_store_t;


/*
 * Initialize: use default sizes for all components
 */
extern void init_harray_store(int_harray_store_t *store);

/*
 * Delete: free memory
 */
extern void delete_harray_store(int_harray_store_t *store);

/*
 * Reset: remove all elements from hset
 */
extern void reset_harray_store(int_harray_store_t *store);


/*
 * Return the empty set
 */
static inline harray_t *empty_harray(int_harray_store_t *store) {
  return int_array_hset_get(&store->hset, 0, NULL);
}

/*
 * Singleton set { x }
 */
static inline harray_t *singleton_harray(int_harray_store_t *store, int32_t x) {
  return int_array_hset_get(&store->hset, 1, &x);
}

/*
 * Construct the set that contains elements x[0]  ... x[n-1]
 * - this sorts array x and removes duplicates then constructs the harray
 * - x may be modified.
 */
extern harray_t *make_harray(int_harray_store_t *store, uint32_t n, int32_t *x);

/*
 * Construct the union of two sets
 * - a and b must be from the store
 */
extern harray_t *merge_two_harrays(int_harray_store_t *store, harray_t *a, harray_t *b);

/*
 * Construct the union of n sets a[0 ... n-1]
 * - a may be modified
 * - return the empty set if n is zero
 */
extern harray_t *merge_harrays(int_harray_store_t *store, harray_t **a, uint32_t n);

/*
 * Return a - { x[0] .... x[n-1] }
 */
extern harray_t *harray_remove_elem(int_harray_store_t *store, harray_t *a, uint32_t n, int32_t *x);


/*
 * Remove arrays that satisfy f (cf. int_array_hsets.h)
 */
static inline void harray_store_remove_arrays(int_harray_store_t *store, void *aux, int_array_hset_filter_t f) {
  int_array_hset_remove_arrays(&store->hset, aux, f);
}


#endif /* __INT_HARRAY_STORE_H */
