/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * BINARY HEAP OF INTEGERS WITH CUSTOMIZABLE ORDERING
 * - stores a set of integers, all in range [0 ... n]
 * - the ordering is defined by a function provided when
 *   the heap is constructed
 */

#ifndef __GENERIC_HEAP_H
#define __GENERIC_HEAP_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>


/*
 * Function type for comparison functions
 * - the function is called as cmp(user_data, x, y)
 *   where x and y are distinct elements in the heap
 * - it must return true for x < y, false otherwise
 * - user_data is a generic void * pointer
 */
typedef bool (* heap_cmp_fun_t)(void *data, int32_t x, int32_t y);


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
 *
 * The ordering is defined by heap->cmp and heap->data
 * - both are setup when the heap is initialized
 */
typedef struct generic_heap_s {
  // the heap itself
  int32_t *heap;
  uint32_t nelems;
  uint32_t size;
  // index array and its size
  int32_t *idx;
  uint32_t idx_size;
  // ordering
  heap_cmp_fun_t cmp;
  void *data;
} generic_heap_t;

#define DEF_GENERIC_HEAP_SIZE 80
#define MAX_GENERIC_HEAP_SIZE (UINT32_MAX/4)

#define DEF_GENERIC_HEAP_IDX_SIZE 80
#define MAX_GENERIC_HEAP_IDX_SIZE (UINT32_MAX/4)



/*
 * Initialize heap:
 * - n = initial size. If n=0, the default is used.
 * - m = initial size of idx. If m=0, the default is used.
 * - cmp = the comparison function
 * - data = some data used for computing the ordering
 */
extern void init_generic_heap(generic_heap_t *heap, uint32_t n, uint32_t m,
                              heap_cmp_fun_t cmp, void *data);


/*
 * Delete: free all memory
 */
extern void delete_generic_heap(generic_heap_t *heap);


/*
 * Empty the heap
 */
extern void reset_generic_heap(generic_heap_t *heap);


/*
 * Add element x: do nothing is x is in the heap already
 * - x must be non-negative
 */
extern void generic_heap_add(generic_heap_t *heap, int32_t x);


/*
 * Remove element x. Do nothing if x is not in the heap
 * - x must be non-negative
 */
extern void generic_heap_remove(generic_heap_t *heap, int32_t x);


/*
 * Check whether the heap is empty
 */
static inline bool generic_heap_is_empty(generic_heap_t *heap) {
  return heap->nelems == 0;
}


/*
 * Number of elements
 */
static inline uint32_t generic_heap_nelems(generic_heap_t *heap) {
  return heap->nelems;
}



/*
 * Check whether x is in the heap
 */
static inline bool generic_heap_member(generic_heap_t *heap, int32_t x) {
  assert(0 <= x);
  return x < heap->idx_size && heap->idx[x] >= 0;
}

/*
 * Get the minimal element and remove it from the heap
 * - return -1 if the heap is empty
 */
extern int32_t generic_heap_get_min(generic_heap_t *heap);


/*
 * Return the minimal element but don't remove it
 * - return -1 if the heap is empty
 */
static inline int32_t generic_heap_top(generic_heap_t *heap) {
  return heap->nelems == 0 ? -1 : heap->heap[1];
}



/*
 * Update functions allow the position of an element x to change in
 * the ordering.
 * - move_up: if x is now smaller in the ordering (closer to min)
 * - move_down: if x is now larger in the ordering (further from min)
 * - update x: general form.
 * For all three functions, x must be present in the heap
 */
extern void generic_heap_move_up(generic_heap_t *heap, int32_t x);
extern void generic_heap_move_down(generic_heap_t *heap, int32_t x);
extern void generic_heap_update(generic_heap_t *heap, int32_t x);



#endif /* __GENERIC_HEAP_H */
