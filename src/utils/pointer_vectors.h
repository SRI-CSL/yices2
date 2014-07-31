/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * VECTORS OF POINTERS WITH HIDDEN HEADER
 */

#ifndef __POINTER_VECTORS_H
#define __POINTER_VECTORS_H

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>

#include "utils/memalloc.h"


// Header + array
typedef struct ptr_vector_s {
  uint32_t capacity;  // size of data array
  uint32_t size;      // number of elements
  void *data[0];      // real size = capacity
} ptr_vector_t;


/*
 * Access to the header
 */
static inline ptr_vector_t *pv_header(void **v) {
  return (ptr_vector_t *) (((char *) v) - offsetof(ptr_vector_t, data));
}

static inline uint32_t pv_size(void **v) {
  return pv_header(v)->size;
}

static inline uint32_t pv_capacity(void **v) {
  return pv_header(v)->capacity;
}


/*
 * Default and maximal size
 */
#define DEF_PTR_VECTOR_SIZE 10
#define MAX_PTR_VECTOR_SIZE (((uint32_t)(UINT32_MAX - sizeof(ptr_vector_t)))/8)


/*
 * Add elem p at the end of vector *v
 * - if *v is NULL, allocate a fresh vector of default size
 */
extern void add_ptr_to_vector(void ***v, void *p);


/*
 * Increase v's capacity for at least n elements
 * - if *v is NULL, a fresh vector of capacity = max(n, default size) is allocated
 * - if *v is large enough already, nothing is done
 * The size of v is not changed.
 */
extern void resize_ptr_vector(void ***v, uint32_t n);



/*
 * Delete vector v
 */
static inline void delete_ptr_vector(void **v) {
  if (v != NULL) {
    safe_free(pv_header(v));
  }
}


/*
 * Empty vector v
 */
static inline void reset_ptr_vector(void **v) {
  if (v != NULL) {
    pv_header(v)->size = 0;
  }
}


/*
 * Keep only the n first elements of v
 * - v must be non NULL
 * - n must be <= size of v
 */
static inline void ptr_vector_shrink(void **v, uint32_t n) {
  assert(v != NULL && pv_size(v) >= n);
  pv_header(v)->size = n;
}



/*
 * Remove the last element of v
 * - v must be non-null and non-empty
 */
static inline void ptr_vector_pop(void **v) {
  assert(v != NULL && pv_size(v) > 0);
  pv_header(v)->size --;
}


/*
 * Get the last element of v
 * - v must be non-null and non-empty
 */
static inline void *ptr_vector_last(void **v) {
  assert(v != NULL && pv_size(v) > 0);
  return v[pv_size(v) - 1];
}


#endif /* __POINTER_VECTORS_H */
