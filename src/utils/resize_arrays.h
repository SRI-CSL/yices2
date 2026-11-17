/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * RESIZABLE ARRAYS OF INTEGERS
 */

#ifndef __RESIZE_ARRAYS_H
#define __RESIZE_ARRAYS_H

#include <assert.h>
#include <stdint.h>

/*
 * An array maps non-negative 32bit integers to 32bit integers.
 * - the content is defined by map[0 ... top-1] and a default value def
 *   array[i] = map[i] if 0 <= i < top
 *   array[i] = def if top <= i
 * - size if the size of array map
 * - we have 0 <= top <= size
 *
 * This is similar to backtrack_arrays, but without support for push
 * and pop.
 */
typedef struct resize_array_s {
  int32_t *map;
  int32_t def;
  uint32_t top;
  uint32_t size;
} resize_array_t;

#define DEF_RESIZE_ARRAY_SIZE 100
#define MAX_RESIZE_ARRAY_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Initialize with def as the default value
 * - no memory is allocated: top and size are both set to 0.
 */
extern void init_resize_array(resize_array_t *a, int32_t def);

/*
 * Delete: free memory
 */
extern void delete_resize_array(resize_array_t *a);

/*
 * Reset to the initial mapping: a[i] = def for all i
 */
extern void reset_resize_array(resize_array_t *a);


/*
 * Write x at index i.
 * - i must be non-negative
 */
extern void resize_array_write(resize_array_t *a, int32_t i, int32_t x);


/*
 * Read the value stored at index i
 * - i must be non-negative
 */
static inline int32_t resize_array_read(const resize_array_t *a, int32_t i) {
  assert(i >= 0);
  return (i < a->top) ? a->map[i] : a->def;
}

/*
 * Direct read and write: i must be between 0 and a->top
 */
static inline int32_t resize_array_get(resize_array_t *a, int32_t i) {
  assert(0 <= i && i < a->top);
  return a->map[i];
}

static inline void resize_array_set(resize_array_t *a, int32_t i, int32_t x) {
  assert(0 <= i && i < a->top);
  a->map[i] = x;
}



#endif /* __RESIZE_ARRAYS_H */
