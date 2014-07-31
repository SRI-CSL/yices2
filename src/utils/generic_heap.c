/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BINRARY HEAP OF INTEGERS
 * - stores a set of integers, all in range [0 ... n]
 * - the ordering is defined by a function provided when
 *   the heap is constructed
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/generic_heap.h"


/*
 * Initialize heap
 * - n = initial size of the heap array. If n =0, use default
 * - m = initial size of the h_idx array. If m=0, use default
 * - cmp = comparison function
 * - data = user data (used by cmp)
 */
void init_generic_heap(generic_heap_t *heap, uint32_t n, uint32_t m, heap_cmp_fun_t cmp, void *data) {
  int32_t *tmp;
  uint32_t i;

  if (n == 0) n = DEF_GENERIC_HEAP_SIZE;
  if (m == 0) m = DEF_GENERIC_HEAP_IDX_SIZE;

  if (n >= MAX_GENERIC_HEAP_SIZE || m >= MAX_GENERIC_HEAP_IDX_SIZE) {
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

  // ordering
  heap->cmp = cmp;
  heap->data = data;
}


/*
 * Increase the heap array size by 50%
 */
static void increase_generic_heap(generic_heap_t *heap) {
  uint32_t n;

  n = heap->size + 1;
  n += n>>1;
  if (n >= MAX_GENERIC_HEAP_SIZE) {
    out_of_memory();
  }
  heap->heap = (int32_t *) safe_realloc(heap->heap, n * sizeof(int32_t));
  heap->size = n;
}

/*
 * Increase the heap index array: make it large enough to store x
 * - new size is max(x+1, 1.5 * old_size)
 */
static void resize_generic_heap_idx(generic_heap_t *heap, int32_t x) {
  int32_t *tmp;
  uint32_t i, n;

  assert(0 <= x);

  n = heap->idx_size + 1;
  n += n >> 1;
  if (n <= x) {
    n = x+1;
  }

  if (n >= MAX_GENERIC_HEAP_IDX_SIZE) {
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
void delete_generic_heap(generic_heap_t *heap) {
  safe_free(heap->heap);
  safe_free(heap->idx);
  heap->heap = NULL;
  heap->idx = NULL;
}



/*
 * Empty the heap
 */
void reset_generic_heap(generic_heap_t *heap) {
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
 * Ordering function
 */
static inline bool heap_lt(generic_heap_t *heap, int32_t x, int32_t y) {
  assert(x >= 0 && y >= 0 && x != y);
  return heap->cmp(heap->data, x, y);
}



/*
 * Move x up in the heap
 * - i = index of an empty slot where x can be added (or current position of x)
 */
static void heap_update_up(generic_heap_t *heap, int32_t x, uint32_t i) {
  int32_t *h, *idx;
  int32_t y;
  uint32_t j;

  assert(1 <= i && i <= heap->nelems && x >= 0);

  h = heap->heap;
  idx = heap->idx;

  j = i>>1; // parent of i
  y = h[j];

  // this loop terminates since h[0] = -1
  while (y >= 0 && heap_lt(heap, x, y)) {
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
 * Move x down in the heap
 * - i = index of an empty slot where x can be added
 */
static void heap_update_down(generic_heap_t *heap, int32_t x, uint32_t i) {
  int32_t *h, *idx;
  int32_t y, z;
  uint32_t j, n;

  h = heap->heap;
  idx = heap->idx;
  n = heap->nelems;

  assert(i <= n);

  j = 2 * i;  // left child of i

  while (j < n) {
    // both children are in the heap (i.e., j+1 <= n)
    // find smallest of left/right child of i
    y = h[j];
    z = h[j+1];
    if (heap_lt(heap, z, y)) {
      j ++;
      y = z;
    }

    // y = smallest child of i, j = its position
    if (heap_lt(heap, x, y)) {
      // store x in position i
      h[i] = x;
      idx[x] = i;
      return;
    }

    // move y up into position i
    h[i] = y;
    idx[y] = i;

    // move to node j
    i = j;
    j <<= 1;
  }

  // final step: j+1 > n
  if (j == n) {
    // left child of i is in the heap
    // x's position is either i or j
    y = h[j];
    if (heap_lt(heap, y, x)) {
      // move y up
      h[i] = y;
      idx[y] = i;
      h[j] = x;
      idx[x] = j;
    } else {
      h[i] = x;
      idx[x] = i;
    }
  } else {
    // no child of i is in the heap
    h[i] = x;
    idx[x] = i;
  }
}




/*
 * Add element x to the heap
 * - x must be non-negative
 * - no change if x is already in the heap
 */
void generic_heap_add(generic_heap_t *heap, int32_t x) {
  uint32_t n;

  assert(x >= 0);

  if (x < heap->idx_size) {
    if (heap->idx[x] >= 0) return; // x already present
  } else {
    resize_generic_heap_idx(heap, x);
  }

  assert(heap->idx[x] == -1);

  n = heap->nelems + 1;
  if (n == heap->size) {
    increase_generic_heap(heap);
  }
  assert(n < heap->size);
  heap->nelems = n;

  heap_update_up(heap, x, n);
}


/*
 * Remove x from the heap
 * - no change if x is not there
 */
void generic_heap_remove(generic_heap_t *heap, int32_t x) {
  uint32_t n;
  int32_t y;

  assert(x >= 0);

  if (x >= heap->idx_size || heap->idx[x] < 0) return; // not there

  // move last element into the subtree of root x
  n = heap->nelems;
  y = heap->heap[n];
  heap->nelems = n - 1;
  if (x != y) {
    heap_update_down(heap, y, heap->idx[x]);
  }
  heap->idx[x] = -1;
}


/*
 * Get the smallest element and remove it
 * - return -1 if the heap is empty
 */
int32_t generic_heap_get_min(generic_heap_t *heap) {
  uint32_t n;
  int32_t x, y;

  n = heap->nelems;
  if (n == 0) return -1;

  x = heap->heap[1];
  y = heap->heap[n];
  heap->nelems = n - 1;
  if (x != y) {
    heap_update_down(heap, y, 1);
  }
  heap->idx[x] = -1;

  return x;
}


/*
 * Move an existing element x up or down
 */
void generic_heap_move_up(generic_heap_t *heap, int32_t x) {
  uint32_t i;

  assert(0 <= x && x < heap->idx_size && heap->idx[x] >= 0);
  i = heap->idx[x];
  heap_update_up(heap, x, i);
}


void generic_heap_move_down(generic_heap_t *heap, int32_t x) {
  uint32_t i;

  assert(0 <= x && x < heap->idx_size && heap->idx[x] >= 0);
  i = heap->idx[x];
  heap_update_down(heap, x, i);
}


void generic_heap_update(generic_heap_t *heap, int32_t x) {
  uint32_t i, n;
  int32_t y;

  assert(0 <= x && x < heap->idx_size && heap->idx[x] >= 0);
  i = heap->idx[x];
  n = heap->nelems;
  if (i == n) {
    heap_update_up(heap, x, i);
  } else {
    // remove x, replace it by y = last heap element
    y = heap->heap[n];
    heap->nelems = n - 1;
    heap_update_down(heap, y, i);
    // put x back in
    heap->nelems = n;
    heap_update_up(heap, x, n);
  }
}
