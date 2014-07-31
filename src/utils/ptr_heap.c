/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * HEAP OF GENERIC OBJECTS
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/ptr_heap.h"



/*
 * Initialize heap
 * - n = initial size. If n=0, the default size is used.
 * - cmp = comparison function
 */
void init_ptr_heap(ptr_heap_t *heap, uint32_t n, ptr_heap_cmp_fun_t cmp) {
  if (n == 0) {
    n = DEF_PTR_HEAP_SIZE; // default size
  }

  if (n >= MAX_PTR_HEAP_SIZE) {
    out_of_memory();
  }

  assert(n > 0);

  heap->heap = (void **) safe_malloc(n * sizeof(void *));
  heap->heap[0] = NULL; // marker
  heap->nelems = 0;
  heap->size = n;
  heap->cmp = cmp;
}


/*
 * Delete
 */
void delete_ptr_heap(ptr_heap_t *heap) {
  safe_free(heap->heap);
  heap->heap = NULL;
}




/*
 * Increate the heap size by 50%
 */
static void extend_ptr_heap(ptr_heap_t *heap) {
  uint32_t n;

  n = heap->size + 1;
  n += n>>1;
  if (n >= MAX_PTR_HEAP_SIZE) {
    out_of_memory();
  }
  heap->heap = (void **) safe_realloc(heap->heap, n * sizeof(void *));
  heap->size = n;
}




/*
 * Add x to the heap
 * - x must be non-NULL
 */
void ptr_heap_add(ptr_heap_t *heap, void *x) {
  void **h;
  void *y;
  uint32_t i, j;

  assert(x != NULL);

  /*
   * Make room for one more element
   */
  i = heap->nelems + 1;
  heap->nelems = i;
  if (i == heap->size) {
    extend_ptr_heap(heap);
  }
  assert(1 <= i && i < heap->size);

  /*
   * Find position of x in the heap, starting at h[i]
   */
  h = heap->heap;
  for (;;) {
    j = i>>1; // parent of i
    y = h[j];
    if (y == NULL || heap->cmp(y, x)) break;
    // x < y so we move x up (and y down)
    h[i] = y;
    i = j;
  }

  h[i] = x;
}



/*
 * Insert x into the heap when heap->heap[1] is empty
 */
static void ptr_heap_update_down(ptr_heap_t *heap, void *x) {
  void **h;
  void *y, *z;
  uint32_t i, j, n;

  assert(x != NULL && heap->nelems >= 1);

  n = heap->nelems;
  h = heap->heap;
  i = 1; // root of the heap
  j = 2; // left child of i

  while (j < n) {
    // both children of i are in the heap, find the smallest one
    y = h[j];
    z = h[j+1];
    if (heap->cmp(z, y)) {
      j ++;
      y = z;
    }

    // h[j] = y = smallest child of node i
    if (heap->cmp(x, y)) {
      // x can go in h[i]
      h[i] = x;
      return;
    }

    // y moves up and we explore the subtree rooted at j
    h[i] = y;
    i = j;     // new root
    j <<= 1;   // left child of i
  }


  // final step: j+1 > n
  if (j == n) {
    // the left child of i is in the heap, no right child
    y = h[j];
    if (heap->cmp(x, y)) {
      h[i] = x;
    } else {
      // move y up and store x into leaf node j
      h[i] = y;
      h[j] = x;
    }

  } else {
    // i is a leaf node
    h[i] = x;
  }
}


/*
 * Remove the smallest element (the root)
 * - return NULL if the heap is empty
 */
void *ptr_heap_get_min(ptr_heap_t *heap) {
  void *x, *y;
  uint32_t n;

  n = heap->nelems;
  if (n == 0) return NULL;

  x = heap->heap[1];  // root
  y = heap->heap[n];  // last leaf
  n --;
  heap->nelems = n;
  if (n > 0) {
    ptr_heap_update_down(heap, y);
  }

  return x;
}


/*
 * Remove the last element (last leaf)
 */
void *ptr_heap_get_elem(ptr_heap_t *heap) {
  void *x;
  uint32_t n;

  n = heap->nelems;
  if (n == 0) return NULL;

  x = heap->heap[n];
  heap->nelems = n-1;

  return x;
}
