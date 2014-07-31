/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * VECTORS OF POINTERS (RESIZABLE ARRAYS)
 */

#ifndef __PTR_VECTORS_H
#define __PTR_VECTORS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

/*
 * Vector of pointers
 * - capacity = size of array data
 * - size = number of elements in the array
 */
typedef struct pvector_s {
  uint32_t capacity;
  uint32_t size;
  void **data;
} pvector_t;


/*
 * Default initial size and max size
 */
#define DEF_PVECTOR_SIZE 10
#define MAX_PVECTOR_SIZE (UINT32_MAX/8)


/*
 * Initialize v with capacity n
 * - the vector is empty
 */
extern void init_pvector(pvector_t *v, uint32_t n);

/*
 * Free all memory used by v
 */
extern void delete_pvector(pvector_t *v);

/*
 * Make v 50% larger: increase its capacity
 * - leave the size and content unchanged.
 */
extern void extend_pvector(pvector_t *v);

/*
 * Make v large enough for n elements:
 * - increase the capacity if needed
 * - kepp the size and content unchanged.
 */
extern void resize_pvector(pvector_t *v, uint32_t n);

/*
 * Copy array a[0 .. n-1] into v
 * - overwrite v's content if it's not empty
 */
extern void pvector_copy(pvector_t *v, void **a, uint32_t n);


/*
 * Add pointer p at the end of v
 */
static inline void pvector_push(pvector_t *v, void *p) {
  uint32_t i;

  i = v->size;
  if (i >= v->capacity) {
    extend_pvector(v);
  }
  v->data[i] = p;
  v->size = i+1;
}


/*
 * Return the last element of v
 */
static inline void *pvector_last(pvector_t *v) {
  assert(v->size > 0);
  return v->data[v->size - 1];
}

/*
 * Remove the last element
 */
static inline void pvector_pop(pvector_t *v) {
  assert(v->size > 0);
  v->size --;
}


/*
 * Combine pop and last: remove and return the last element
 */
static inline void *pvector_pop2(pvector_t *v) {
  assert(v->size > 0);
  v->size --;
  return v->data[v->size];
}

/*
 * Empty the vector
 */
static inline void pvector_reset(pvector_t *v) {
  v->size = 0;
}


/*
 * Keep the first n elements of v
 * - n must be less than or equal to v's size
 */
static inline void pvector_shrink(pvector_t *v, uint32_t n) {
  assert(n <= v->size);
  v->size = n;
}


#endif /* __PTR_VECTORS_H */
