/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Sets/bags of pointers
 * - this supports addition and removal of (void *) pointers.
 *   All elements in the set must be distinct from NULL and 
 *   DELETED_PTR_ELEM (defined below)
 * - the implementation uses an array
 * - if the set is small, we just use linear scan of the array
 * - when the set becomes large, we switch to a hash table
 */

#ifndef __PTR_SETS_H
#define __PTR_SETS_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#include "utils/memalloc.h"


/*
 * Set descriptor:
 * - data = array of n elements where n is a power of two
 * - size = n
 * - nelems = actual number of elements in data
 * - ndeleted = number of deleted elements
 */
typedef struct ptr_set_s {
  uint32_t size;
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  void *data[0]; // real size = size
} ptr_set_t;


#define DEF_PTR_SET_SIZE 8
#define MAX_PTR_SET_SIZE ((UINT32_MAX-sizeof(ptr_set_t))/sizeof(void *))


/*
 * Threshold: when size > SMALL_PTR_SET_SIZE, we switch to
 * a hash-table representation.
 *
 * In hash-table mode, the following thresholds are used:
 * - when nelems > size * PTR_SET_RESIZE_RATIO: make the table larger
 * - when nelems < size * PTR_SET_SHRINK_RATIO: make the table smaller
 */
#define SMALL_PTR_SET_SIZE   32
#define PTR_SET_RESIZE_RATIO 0.7
#define PTR_SET_SHRINK_RATIO 0.3

/*
 * Marker for deleted elements
 */
#define DELETED_PTR_ELEM ((void *) 1)


/*
 * Allocate and initialize a set
 * - this creates an empty set of default size
 */
extern ptr_set_t *new_ptr_set(void);

/*
 * Delete a set descriptor
 */
static inline void free_ptr_set(ptr_set_t *s) {
  safe_free(s);
}



/*
 * Check whether p != NULL && p != DELETED_PTR_ELEM
 */
static inline bool live_ptr_elem(void *p) {
  return (((uintptr_t) p) >> 1) != (uintptr_t) 0;
}


/*
 * Check whether set s contains p
 * - s can be NULL here. NULL is interpreted as the empty set.
 */
extern bool ptr_set_member(ptr_set_t *s, void *p);


/*
 * Add p to the set *s.
 * - p must be distinct from NULL and from DELETED_PTR_ELEM
 * - if *s is NULL, this function creates a new set of
 *   default size that contains the singleton { p } and stores
 *   this new set in *s.
 * - if *s is non NULL, then p is added to the set pointed
 *   to by *s. This may cause of new set descriptor to
 *   be allocated and stored in *s (and the original set
 *   is freed).
 *
 * The function does not check whether p is already present.
 * It will add an element to *s no-matter what (so *s may
 * contain duplicates).
 */
extern void ptr_set_add(ptr_set_t **s, void *p);


/*
 * Remove p from set *s
 * - p must be distinct from NULL and from DELETED_PTR_ELEM
 * - p must be present in *s (so *s must be non-NULL)
 * - *s may be updated to a new set descriptor if the removal
 *   of p causes a reduction in size.
 *
 * If s contains p multiple times, then only one occurrence
 * of p is removed.
 */
extern void ptr_set_remove(ptr_set_t **s, void *p);


/*
 * Add p to *s if it's not present.
 * - updates *s as explained in ptr_set_add
 * - returns true if p is added (i.e., p was not in *s when the function was called)
 * - returns false otherwise and leaves *s unchanged.
 */
extern bool ptr_set_add_if_absent(ptr_set_t **s, void *p);


/*
 * Remove p from *s if it's present
 * - if p is not present in *s, then *s is unchanged and the function
 *   returns false.
 * - otherwise, one occurrence of p is removed from *s, then *s
 *   may be updated as in ptr_set_remove, and the function returns true.
 */
extern bool ptr_set_remove_if_present(ptr_set_t **s, void *p);


/*
 * Iterator: call f(aux, p) for every p stored in s
 * - f must not have a side effect on s
 */
typedef void (*ptr_set_iterator_t)(void *aux, void *p);

extern void ptr_set_iterate(ptr_set_t *s, void *aux, ptr_set_iterator_t f);


#endif /* __PTR_SETS_H */
