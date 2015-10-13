/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BAGS OF NON-NEGATIVE INTEGERS
 * - these are implemented as arrays with a hidden header
 * - the code is similar to indexed_vectors but the bags have
 *   support for efficiently removing elements (using a free list)
 */

#ifndef __INT_BAGS_H
#define __INT_BAGS_H

#include <stddef.h>
#include <stdint.h>

#include "utils/memalloc.h"


/*
 * Header:
 * - cap = size of the array data
 * - size = elements in the array that are used
 * - nelems = number of elements in the array
 * - free = head of the free list
 * We have:
 * - nelems + length(free list) = size <= cap
 * - the free list is implemented using negative integers:
 * - if free = -1 then the free list is empty
 *   otherwise let k = free with sign bit cleared then
 *   k = index of the first list element in data and
 *   data[k] encodes the next index in the same way
 */
typedef struct int_bag_s {
  uint32_t capacity;
  uint32_t size;
  uint32_t nelems;
  int32_t free;
  int32_t data[0];
} int_bag_t;


/*
 * Default and maximal size of an index vector
 */
#define DEF_INT_BAG_SIZE 10
#define MAX_INT_BAG_SIZE (((uint32_t)(UINT32_MAX-sizeof(int_bag_t)))/sizeof(int32_t))



/*
 * Access to the header, given a vector v
 */
static inline int_bag_t *ibag_header(int32_t *v) {
  return (int_bag_t *) (((char *) v) - offsetof(int_bag_t, data));
}

static inline uint32_t ibag_size(int32_t *v) {
  return ibag_header(v)->size;
}

static inline uint32_t ibag_capacity(int32_t *v) {
  return ibag_header(v)->capacity;
}

static inline uint32_t ibag_nelems(int32_t *v) {
  return ibag_header(v)->nelems;
}




/*
 * Add elem k to vector *v
 * - k must be non-negative
 * - if *v is NULL, allocate a fresh bag of default size
 * - return the index i where k is added (such that v[i] = k)
 */
extern int32_t ibag_add(int32_t **v, int32_t k);


/*
 * Delete vector v
 */
static inline void ibag_delete(int32_t *v) {
  if (v != NULL) {
    safe_free(ibag_header(v));
  }
}


/*
 * Empty vector v
 */
extern void ibag_reset(int32_t *v);


/*
 * Remove v[i] from vector v
 * - v must be non NULL and i must satisfy 0 <= i < ibag_size(v)
 * - index i is added to the free list
 */
extern void ibag_clear_elem(int32_t *v, int32_t i);


#endif /* __INT_BAGS_H */
