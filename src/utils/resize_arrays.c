/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * RESIZABLE ARRAYS OF INTEGERS
 */

#include "utils/resize_arrays.h"
#include "utils/memalloc.h"

/*
 * Initialize with def as the default value
 * - no memory is allocated: top and size are both set to 0.
 */
void init_resize_array(resize_array_t *a, int32_t def) {
  a->map = NULL;
  a->def = def;
  a->top = 0;
  a->size = 0;
}

/*
 * Delete: free memory
 */
void delete_resize_array(resize_array_t *a) {
  safe_free(a->map);
  a->map = NULL;
}

/*
 * Reset to the initial mapping: a[i] = def for all i
 */
void reset_resize_array(resize_array_t *a) {
  a->top = 0;
}


/*
 * Increase the size
 */
static void extend_resize_array(resize_array_t *a) {
  uint32_t n;

  n = a->size;
  if (n == 0) {
    // first allocation
    n = DEF_RESIZE_ARRAY_SIZE;
    assert(n <= MAX_RESIZE_ARRAY_SIZE);
    a->map = (int32_t *) safe_malloc(n * sizeof(int32_t));
    a->size = n;
  } else {
    // try to increase the size by 50%
    n += n>>1;
    if (n > MAX_RESIZE_ARRAY_SIZE) {
      out_of_memory();
    }
    a->map = (int32_t *) safe_realloc(a->map, n * sizeof(int32_t));
    a->size = n;
  }
}

/*
 * Move top to index n
 * - n must be no more than a->size
 * - a->map[top ... n-1] are set to a->def
 */
static void move_resize_array_top(resize_array_t *a, uint32_t n) {
  uint32_t i;

  assert(a->top < n && n <= a->size);

  for (i=a->top; i<n; i++) {
    a->map[i] = a->def;
  }
  a->top = n;
}


/*
 * Write x at index i.
 * - i must be non-negative
 */
void resize_array_write(resize_array_t *a, int32_t i, int32_t x) {
  assert(i >= 0);
  assert(a->top <= a->size);

  if (i >= a->size) extend_resize_array(a);
  // i < a->size <= MAX_RESIZE_ARRAY_SIZE so i+1 can't overflow here.
  if (i >= a->top) move_resize_array_top(a, i+1);

  a->map[i] = x;
}

