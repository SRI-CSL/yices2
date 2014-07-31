/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BINARY HEAP FOR GENERIC OBJECTS
 *
 * The heap stores pointers to objects.
 * The order between these objects is defined when the heap is
 * initialized.
 */

#ifndef __PTR_HEAP_H
#define __PTR_HEAP_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Comparison function:
 * - the function is called as cmp(x, y) where x and y
 *   pointers to two objects in the heap
 * - it must return true if (x <= y), false otherwise
 * Heap property:
 * - h[i] has two siblings h[2i] and h[2i+1] such that
 *   cmp(h[i], h[2i]) and cmp(h[i], h[2i+1]) are both true
 */
typedef bool (* ptr_heap_cmp_fun_t)(void *x, void *y);


/*
 * Heap structure
 * - nelems = number of elements stored in the heap
 * - heap = array of pointers
 *   heap[0] is a marker (always NULL)
 *   heap[1 ... nelems] contains the rest (as a binary tree)
 * - size = full size of array heap
 * - cmp = the comparison function
 */
typedef struct ptr_heap_s {
  // the heap itself
  void **heap;
  uint32_t nelems;
  uint32_t size;
  // function pointer for the ordering
  ptr_heap_cmp_fun_t cmp;
} ptr_heap_t;

#define DEF_PTR_HEAP_SIZE 40
#define MAX_PTR_HEAP_SIZE (UINT32_MAX/sizeof(void*))



/*
 * Initialize heap:
 * - n = initial size. If n=0, the default is used.
 * - cmp = the comparison function to use.
 */
extern void init_ptr_heap(ptr_heap_t *heap, uint32_t n, ptr_heap_cmp_fun_t cmp);


/*
 * Delete: free all memory
 */
extern void delete_ptr_heap(ptr_heap_t *heap);


/*
 * Empty the heap
 */
static inline void reset_ptr_heap(ptr_heap_t *heap) {
  heap->nelems = 0;
}


/*
 * Add element x
 * - x must be non-NULL
 * - the object pointed to by x should not be modified as long
 *   as x is in the heap (at least not in a way that changes
 *   the order).
 */
extern void ptr_heap_add(ptr_heap_t *heap, void *x);


/*
 * Check whether the heap is empty
 */
static inline bool ptr_heap_is_empty(ptr_heap_t *heap) {
  return heap->nelems == 0;
}


/*
 * Get the number of elements in the heap
 */
static inline uint32_t ptr_heap_nelems(ptr_heap_t *heap) {
  return heap->nelems;
}



/*
 * Get the minimal element and remove it from the heap
 * - return NULL if the heap is empty
 */
extern void *ptr_heap_get_min(ptr_heap_t *heap);


/*
 * Extract and remove an arbitrary element from the heap
 * (this always returns the last leaf)
 * - return NULL if the heap is empty
 * This can be used to cheaply extract all elements one by one.
 * (e.g., to delete them).
 */
extern void *ptr_heap_get_elem(ptr_heap_t *heap);


#endif /* __PTR_HEAP_H */
