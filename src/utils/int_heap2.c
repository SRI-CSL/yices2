/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BINARY HEAP OF INTEGERS WITH CUSTOMIZABLE ORDERING
 */

#include <assert.h>

#include "utils/int_heap2.h"
#include "utils/memalloc.h"



/*
 * Initialize heap
 * - n = initial size. If n=0, the default size is used.
 * - cmp = comparison function
 */
void init_int_heap2(int_heap2_t *heap, uint32_t n, int_heap_cmp_fun_t cmp, void *data) {
  if (n == 0) {
    n = DEF_INT_HEAP2_SIZE; // default size
  }

  if (n >= MAX_INT_HEAP2_SIZE) {
    out_of_memory();
  }

  assert(n > 0);

  heap->heap = (int32_t *) safe_malloc(n * sizeof(int32_t));
  heap->heap[0] = 0;
  heap->nelems = 0;
  heap->size = n;
  heap->cmp = cmp;
  heap->data = data;
}


/*
 * Delete
 */
void delete_int_heap2(int_heap2_t *heap) {
  safe_free(heap->heap);
  heap->heap = NULL;
}




/*
 * Increate the heap size by 50%
 */
static void extend_int_heap2(int_heap2_t *heap) {
  uint32_t n;

  n = heap->size + 1;
  n += n>>1;
  if (n >= MAX_INT_HEAP2_SIZE) {
    out_of_memory();
  }
  heap->heap = (int32_t *) safe_realloc(heap->heap, n * sizeof(int32_t));
  heap->size = n;
}




/*
 * Add x to the heap
 */
void int_heap2_add(int_heap2_t *heap, int32_t x) {
  int32_t *h;
  int32_t y;
  uint32_t i, j;


  /*
   * Make room for one more element
   */
  i = heap->nelems + 1;
  heap->nelems = i;
  if (i == heap->size) {
    extend_int_heap2(heap);
  }
  assert(1 <= i && i < heap->size);

  /*
   * Find position of x in the heap, starting at h[i]
   */
  h = heap->heap;
  for (;;) {
    j = i>>1; // parent of i
    y = h[j];
    if (j == 0 || heap->cmp(heap->data, y, x)) break;
    // x < y so we move x up (and y down)
    h[i] = y;
    i = j;
  }

  h[i] = x;
}



/*
 * Insert x into the heap when heap->heap[1] is empty
 */
static void int_heap2_update_down(int_heap2_t *heap, int32_t x) {
  int32_t *h;
  int32_t y, z;
  uint32_t i, j, n;

  assert(heap->nelems >= 1);

  n = heap->nelems;
  h = heap->heap;
  i = 1; // root of the heap
  j = 2; // left child of i

  while (j < n) {
    // both children of i are in the heap, find the smallest one
    y = h[j];
    z = h[j+1];
    if (heap->cmp(heap->data, z, y)) {
      j ++;
      y = z;
    }

    // h[j] = y = smallest child of node i
    if (heap->cmp(heap->data, x, y)) {
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
    if (heap->cmp(heap->data, x, y)) {
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
 */
int32_t int_heap2_get_min(int_heap2_t *heap) {
  int32_t x, y;
  uint32_t n;

  n = heap->nelems;
  assert(n > 0);

  x = heap->heap[1];  // root
  y = heap->heap[n];  // last leaf
  n --;
  heap->nelems = n;
  if (n > 0) {
    int_heap2_update_down(heap, y);
  }

  return x;
}
