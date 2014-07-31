/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BINARY HEAP OF INTEGERS
 *
 * Heap of 32bit signed integers with customizable ordering
 * This module is similar to ptr_heap for integers. It's
 * simpler than generic heap and can contain several times
 * the same integer.
 */

#ifndef __INT_HEAP2_H
#define __INT_HEAP2_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Comparison function:
 * - the function is called as cmp(user_data, x, y) where
 *   x and y are two integers in the heap
 * - it must return true if (x <= y), false otherwise
 * - user_data is a generic void* pointer set up when the heap is
 *   initialized
 * Heap property:
 * - h[i] has two children h[2i] and h[2i+1] such that
 *   cmp(h[i], h[2i]) and cmp(h[i], h[2i+1]) are both true
 */
typedef bool (* int_heap_cmp_fun_t)(void *data, int32_t x, int32_t y);


/*
 * Heap structure
 * - nelems = number of elements stored in the heap
 * - heap = array of pointers
 *   heap[0] is always 0
 *   heap[1 ... nelems] contains the rest (as a binary tree)
 * - size = full size of array heap
 * - cmp = the comparison function
 */
typedef struct int_heap2_s {
  // the heap itself
  int32_t *heap;
  uint32_t nelems;
  uint32_t size;
  // function pointer + user data for the ordering
  int_heap_cmp_fun_t cmp;
  void *data;
} int_heap2_t;

#define DEF_INT_HEAP2_SIZE 40
#define MAX_INT_HEAP2_SIZE (UINT32_MAX/sizeof(int32_t))



/*
 * Initialize heap:
 * - n = initial size. If n=0, the default is used.
 * - cmp = the comparison function to use.
 * - data = pointer to the object to pass as first argument of cmp
 */
extern void init_int_heap2(int_heap2_t *heap, uint32_t n, int_heap_cmp_fun_t cmp, void *data);


/*
 * Delete: free all memory
 */
extern void delete_int_heap2(int_heap2_t *heap);


/*
 * Empty the heap
 */
static inline void reset_int_heap2(int_heap2_t *heap) {
  heap->nelems = 0;
}


/*
 * Change the ordering functions:
 * - cmp = comparison function
 *   data = auxiliary data used for comparisons
 * - the heap must be empty when this is called
 */
static inline void int_heap2_reset_order(int_heap2_t *heap, int_heap_cmp_fun_t cmp, void *data) {
  assert(heap->nelems == 0);
  heap->cmp = cmp;
  heap->data = data;
}


/*
 * Add element x
 */
extern void int_heap2_add(int_heap2_t *heap, int32_t x);


/*
 * Check whether the heap is empty
 */
static inline bool int_heap2_is_empty(int_heap2_t *heap) {
  return heap->nelems == 0;
}


/*
 * Get the number of elements in the heap
 */
static inline uint32_t int_heap2_nelems(int_heap2_t *heap) {
  return heap->nelems;
}


/*
 * Get the minimal element and remove it from the heap
 * - heap must be non-empty
 */
extern int32_t int_heap2_get_min(int_heap2_t *heap);




#endif /* __INT_HEAP2_H */
