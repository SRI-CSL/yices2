/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * VECTORS OF INTEGERS (RESIZABLE ARRAYS)
 */

#ifndef __INT_VECTORS_H
#define __INT_VECTORS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>


/*
 * Vector of signed 32bit integers
 * - capacity = size of the data array
 * - size = number of elements stored in data
 *   (i.e., the vector's content is data[0 ... size-1])
 */
typedef struct ivector_s {
  uint32_t capacity;
  uint32_t size;
  int32_t *data;
} ivector_t;


/*
 * Default initial size and max size
 */
#define DEF_IVECTOR_SIZE 10
#define MAX_IVECTOR_SIZE (UINT32_MAX/sizeof(int32_t))



/*
 * Initialize v with initial capacity = n
 * - v is empty
 */
extern void init_ivector(ivector_t *v, uint32_t n);

/*
 * Free the memory used by v
 */
extern void delete_ivector(ivector_t *v);

/*
 * Increase v's capacity by 50% (approximately)
 * Keep the content and size unchanged.
 */
extern void extend_ivector(ivector_t *v);

/*
 * Make v large enough for at least n elements
 * - increase the capacity if needed
 * - keep the content and size unchanged.
 */
extern void resize_ivector(ivector_t *v, uint32_t n);

/*
 * copy array a[0 .. n-1] into v
 */
extern void ivector_copy(ivector_t *v, const int32_t *a, uint32_t n);

/*
 * append a[0 .. n-1] to v
 */
extern void ivector_add(ivector_t *v, const int32_t *a, uint32_t n);


/*
 * Swap the content of v1 and v2
 */
extern void ivector_swap(ivector_t *v1, ivector_t *v2);


/*
 * add x at the end of v
 */
static inline void ivector_push(ivector_t *v, int32_t x) {
  uint32_t i;

  i = v->size;
  if (i >= v->capacity) {
    extend_ivector(v);
  }
  v->data[i] = x;
  v->size = i+1;
}

/*
 * get the last element
 */
static inline int32_t ivector_last(ivector_t *v) {
  assert(v->size > 0);
  return v->data[v->size - 1];
}

/*
 * remove the last element
 */
static inline void ivector_pop(ivector_t *v) {
  assert(v->size > 0);
  v->size --;
}

/*
 * combine pop and last: remove and return the last element
 */
static inline int32_t ivector_pop2(ivector_t *v) {
  assert(v->size > 0);
  v->size --;
  return v->data[v->size];
}

/*
 * Empty v
 */
static inline void ivector_reset(ivector_t *v) {
  v->size = 0;
}


/*
 * Keep the n first elements of v
 * - n must be less than or equal to v's current size.
 */
static inline void ivector_shrink(ivector_t *v, uint32_t n) {
  assert(n <= v->size);
  v->size = n;
}


/*
 * Remove duplicates in an integer vector
 * Side effect: sort v in increasing order
 */
extern void ivector_remove_duplicates(ivector_t *v);

#endif /* _INT__VECTORS_H */
