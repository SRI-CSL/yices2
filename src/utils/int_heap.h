/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BINARY HEAP OF INTEGERS
 * - stores a set of integers, all in range [0 ... n]
 * - elements are extracted in increasing order
 */

#ifndef __INT_HEAP_H
#define __INT_HEAP_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>


/*
 * Heap structure
 * - nelems = number of elements stored in the heap
 * - heap = array of integers
 *   heap[0] is a marker
 *   heap[1 ... nelems] contains the rest (as a binary tree)
 * - idx = array [0 ... n]:
 *   if x is in the heap then idx[x] = i such that heap[i] = x
 *   if x is not in the heap then idx[x] = -1
 * - size = full size of array heap
 * - idx_size = size of the heap_index array
 */
typedef struct int_heap_s {
  // the heap itself
  int32_t *heap;
  uint32_t nelems;
  uint32_t size;
  // index array and its size
  int32_t *idx;
  uint32_t idx_size;
} int_heap_t;

#define DEF_INT_HEAP_SIZE 80
#define MAX_INT_HEAP_SIZE (UINT32_MAX/4)

#define DEF_INT_HEAP_IDX_SIZE 80
#define MAX_INT_HEAP_IDX_SIZE (UINT32_MAX/4)


/*
 * Initialize heap:
 * - n = initial size. If n=0, the default is used.
 * - m = initial size of h_idx. If m=0, the default is used.
 */
extern void init_int_heap(int_heap_t *heap, uint32_t n, uint32_t m);


/*
 * Delete: free all memory
 */
extern void delete_int_heap(int_heap_t *heap);


/*
 * Empty the heap
 */
extern void reset_int_heap(int_heap_t *heap);


/*
 * Add element x: do nothing if x is in the heap already
 * - x must be non-negative
 */
extern void int_heap_add(int_heap_t *heap, int32_t x);


/*
 * Remove element x. Do nothing is x is not in the heap
 * - x must be non-negative
 */
extern void int_heap_remove(int_heap_t *heap, int32_t x);


/*
 * Check whether the heap is empty
 */
static inline bool int_heap_is_empty(int_heap_t *heap) {
  return heap->nelems == 0;
}


/*
 * Get the number of elements in the heap
 */
static inline uint32_t int_heap_nelems(int_heap_t *heap) {
  return heap->nelems;
}


/*
 * Check whether x is in the heap
 */
static inline bool int_heap_member(int_heap_t *heap, int32_t x) {
  assert(0 <= x);
  return x < heap->idx_size && heap->idx[x] >= 0;
}


/*
 * Get the minimal element and remove it from the heap
 * - return -1 if the heap is empty
 */
extern int32_t int_heap_get_min(int_heap_t *heap);



#endif /* __INT_HEAP_H */
