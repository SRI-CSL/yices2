/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * VECTORS OF VALUES (RESIZABLE ARRAYS)
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "mcsat/value.h"

/*
 * Vector of values integers
 * - capacity = size of the data array
 * - size = number of elements stored in data
 *   (i.e., the vector's content is data[0 ... size-1])
 */
typedef struct value_vector_s {
  uint32_t capacity;
  uint32_t size;
  mcsat_value_t *data;
} value_vector_t;


/*
 * Initialize v with initial capacity = n
 * - v is empty
 */
extern void init_value_vector(value_vector_t *v, uint32_t n);

/*
 * Free the memory used by v
 */
extern void delete_value_vector(value_vector_t *v);

/*
 * Increase v's capacity by 50% (approximately)
 * Keep the content and size unchanged.
 */
extern void extend_value_vector(value_vector_t *v);

/*
 * Make v large enough for at least n elements
 * - increase the capacity if needed
 * - keep the content and size unchanged.
 */
extern void resize_value_vector(value_vector_t *v, uint32_t n);

/*
 * Swap the content of v1 and v2
 */
extern void value_vector_swap(value_vector_t *v1, value_vector_t *v2);


/*
 * add x at the end of v (constructs empty)
 */
static inline mcsat_value_t* value_vector_push(value_vector_t *v) {
  uint32_t i;

  i = v->size;
  if (i >= v->capacity) {
    extend_value_vector(v);
  }
  mcsat_value_construct_default(v->data + i);
  v->size = i+1;

  return v->data + i;
}

/*
 * get the last element
 */
static inline mcsat_value_t* value_vector_last(value_vector_t *v) {
  assert(v->size > 0);
  return v->data + v->size - 1;
}

/*
 * remove the last element
 */
static inline void value_vector_pop(value_vector_t *v) {
  assert(v->size > 0);
  v->size --;
  mcsat_value_destruct(v->data + v->size);
}

/*
 * Empty v
 */
static inline void value_vector_reset(value_vector_t *v) {
  uint32_t i;
  for (i = 0; i < v->size; ++ i) {
    mcsat_value_destruct(v->data + i);
  }
  v->size = 0;
}

/*
 * Keep the n first elements of v
 * - n must be less than or equal to v's current size.
 */
static inline void value_vector_shrink(value_vector_t *v, uint32_t n) {
  assert(n <= v->size);
  uint32_t i;
  for (i = n; i < v->size; ++ i) {
    mcsat_value_destruct(v->data + i);
  }
  v->size = n;
}

