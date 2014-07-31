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

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/int_heap.h"


/*
 * Initialize heap
 * - n = initial size of the heap array. If n =0, use default
 * - m = initial size of the h_idx array. If m=0, use default
 */
void init_int_heap(int_heap_t *heap, uint32_t n, uint32_t m) {
  int32_t *tmp;
  uint32_t i;

  if (n == 0) n = DEF_INT_HEAP_SIZE;
  if (m == 0) m = DEF_INT_HEAP_IDX_SIZE;

  if (n >= MAX_INT_HEAP_SIZE || m >= MAX_INT_HEAP_IDX_SIZE) {
    out_of_memory();
  }

  assert(n > 0);

  heap->heap = (int32_t *) safe_malloc(n * sizeof(int32_t));
  heap->heap[0] = -1; // marker
  heap->nelems = 0;
  heap->size = n;

  // index array: initialized to -1 everywhere
  tmp = (int32_t *) safe_malloc(m * sizeof(int32_t));
  for (i=0; i<m; i++) {
    tmp[i] = -1;
  }
  heap->idx = tmp;
  heap->idx_size = m;
}


/*
 * Increase the heap array size by 50%
 */
static void increase_int_heap(int_heap_t *heap) {
  uint32_t n;

  n = heap->size + 1;
  n += n>>1;
  if (n >= MAX_INT_HEAP_SIZE) {
    out_of_memory();
  }
  heap->heap = (int32_t *) safe_realloc(heap->heap, n * sizeof(int32_t));
  heap->size = n;
}

/*
 * Increase the heap index array: make it large enough to store x
 * - new size is max(x+1, 1.5 * old_size)
 */
static void resize_int_heap_idx(int_heap_t *heap, int32_t x) {
  int32_t *tmp;
  uint32_t i, n;

  assert(0 <= x);

  n = heap->idx_size + 1;
  n += n >> 1;
  if (n <= x) {
    n = x+1;
  }

  if (n >= MAX_INT_HEAP_IDX_SIZE) {
    out_of_memory();
  }

  tmp = safe_realloc(heap->idx, n * sizeof(int32_t));
  for (i=heap->idx_size; i<n; i++) {
    tmp[i] = -1;
  }
  heap->idx = tmp;
  heap->idx_size = n;
}


/*
 * Delete all allocated memory
 */
void delete_int_heap(int_heap_t *heap) {
  safe_free(heap->heap);
  safe_free(heap->idx);
  heap->heap = NULL;
  heap->idx = NULL;
}



/*
 * Empty the heap
 */
void reset_int_heap(int_heap_t *heap) {
  int32_t *h, *idx;
  uint32_t i, n;
  int32_t x;

  h = heap->heap;
  idx = heap->idx;

  // reset the indices to -1
  n = heap->nelems;
  for (i=1; i<=n; i++) {
    x = h[i];
    idx[x] = -1;
  }

  heap->nelems = 0;
}



/*
 * Move x up in the heap
 * - i = index of an empty slot where x can be added
 */
static void heap_update_up(int_heap_t *heap, int32_t x, uint32_t i) {
  int32_t *h, *idx;
  int32_t y;
  uint32_t j;

  assert(1 <= i && i <= heap->nelems && x >= 0);

  h = heap->heap;
  idx = heap->idx;

  j = i>>1; // parent of i
  y = h[j];

  // this loop terminates since h[0] = -1 < x
  while (x < y) {
    // move y into position i
    h[i] = y;
    idx[y] = i;
    // next parent
    i = j;
    j >>= 1;
    y = h[j];
  }

  // i = new position for x
  h[i] = x;
  idx[x] = i;
}


/*
 * Remove element at position i in the heap
 * - replace it by the current last element
 */
static void heap_update_down(int_heap_t *heap, uint32_t i) {
  int32_t *h, *idx;
  int32_t x, y, z;
  uint32_t j, n;

  h = heap->heap;
  idx = heap->idx;
  n = heap->nelems;
  heap->nelems = n - 1;

  assert(i <= n);

  if (i == n) return; // the last element was removed

  z = h[n];   // current last element
  j = 2 * i;  // left child of i

  while (j + 1 < n) {
    // find smallest of left/right child of i
    x = h[j];
    y = h[j+1];
    if (y < x) {
      j ++;
      x = y;
    }
    // x = smallest child of i, j = its position
    if (z < x) {
      // store z in position i
      h[i] = z;
      idx[z] = i;
      return;
    }

    // move x up into position i
    h[i] = x;
    idx[x] = i;

    // move to node j
    i = j;
    j <<= 1;
  }

  // final step: j+1 >= n
  if (j < n) {
    // z's position is either i or j
    x = h[j];
    if (x < z) {
      // move x up
      h[i] = x;
      idx[x] = i;
      h[j] = z;
      idx[z] = j;
    } else {
      h[i] = z;
      idx[z] = i;
    }
  } else {
    h[i] = z;
    idx[z] = i;
  }
}




/*
 * Add element x to the heap
 * - x must be non-negative
 * - no change if x is already in the heap
 */
void int_heap_add(int_heap_t *heap, int32_t x) {
  uint32_t n;

  assert(x >= 0);

  if (x < heap->idx_size) {
    if (heap->idx[x] >= 0) return; // x already present
  } else {
    resize_int_heap_idx(heap, x);
  }

  assert(heap->idx[x] == -1);

  n = heap->nelems + 1;
  if (n == heap->size) {
    increase_int_heap(heap);
  }
  assert(n < heap->size);
  heap->nelems = n;

  heap_update_up(heap, x, n);
}


/*
 * Remove x from the heap
 * - no change if x is not there
 */
void int_heap_remove(int_heap_t *heap, int32_t x) {
  assert(x >= 0);
  if (x >= heap->idx_size || heap->idx[x] < 0) return; // not there

  heap_update_down(heap, heap->idx[x]);
  heap->idx[x] = -1;
}


/*
 * Get the smallest element and remove it
 * - return -1 if the heap is empty
 */
int32_t int_heap_get_min(int_heap_t *heap) {
  uint32_t n;
  int32_t x;

  n = heap->nelems;
  if (n == 0) return -1;

  x = heap->heap[1];
  heap_update_down(heap, 1);
  heap->idx[x] = -1;

  return x;
}
