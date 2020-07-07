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
 * VECTORS OF INTEGERS
 *
 * Unlike ivector_t defined in vectors.h these index vectors
 * have a hidden header.
 */

#ifndef __INDEX_VECTORS_H
#define __INDEX_VECTORS_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>

#include "utils/memalloc.h"


typedef struct index_vector_s {
  uint32_t capacity;
  uint32_t size;
  int32_t data[0]; // real size is 'capacity'
} index_vector_t;



/*
 * Access to the header, given a vector v
 */
static inline index_vector_t *iv_header(int32_t *v) {
  return (index_vector_t *) (((char *) v) - offsetof(index_vector_t, data));
}

static inline uint32_t iv_size(int32_t *v) {
  return iv_header(v)->size;
}

static inline uint32_t iv_capacity(int32_t *v) {
  return iv_header(v)->capacity;
}


/*
 * Default and maximal size of an index vector
 */
#define DEF_IDX_VECTOR_SIZE 10
#define MAX_IDX_VECTOR_SIZE (((uint32_t)(UINT32_MAX-sizeof(index_vector_t)))/4)


/*
 * Add elem k at the end of vector *v
 * - if *v is NULL, allocate a fresh vector of default size
 */
extern void add_index_to_vector(int32_t **v, int32_t k);


/*
 * Make v large enough for at least n elements
 * - if *v is NULL, a fresh vector of size = max(n, default size) is allocated
 * - if *v is large enough already, nothing is done
 * Keep the current size unchanged (set it to 0 is *v was NULL)
 */
extern void resize_index_vector(int32_t **v, uint32_t n);


/*
 * Create a vector that contains a[0 ... n-1]
 */
extern int32_t *make_index_vector(int32_t *a, uint32_t n);


/*
 * Delete vector v
 */
static inline void delete_index_vector(int32_t *v) {
  if (v != NULL) {
    safe_free(iv_header(v));
  }
}


/*
 * Length
 */
static inline uint32_t iv_len(int32_t *v) {
  return (v == NULL) ? 0 : iv_size(v);
}


/*
 * Test emptiness
 */
static inline bool iv_is_empty(int32_t *v) {
  return v == NULL || iv_size(v) == 0;
}

/*
 * Empty vector v
 */
static inline void reset_index_vector(int32_t *v) {
  if (v != NULL) {
    iv_header(v)->size = 0;
  }
}


/*
 * Keep only the n first elements of v
 * - v must be non NULL
 * - n must be <= size of v
 */
static inline void index_vector_shrink(int32_t *v, uint32_t n) {
  assert(v != NULL && iv_size(v) >= n);
  iv_header(v)->size = n;
}



/*
 * Remove the last element of v
 * - v must be non-null and nonempty
 */
static inline void index_vector_pop(int32_t *v) {
  assert(v != NULL && iv_size(v) > 0);
  iv_header(v)->size --;
}


/*
 * Get the last element of v
 * - v must be non-null and nonempty
 */
static inline int32_t index_vector_last(int32_t *v) {
  assert(v != NULL && iv_size(v) > 0);
  return v[iv_size(v) - 1];
}


/*
 * Remove v[i] from vector v
 * - v must be non NULL and i must satisfy 0 <= i < iv_size(v)
 * - this may swap elements so the order in v is not preserved
 */
extern void clear_index_elem(int32_t *v, uint32_t i);


/*
 * Remove k from vector v
 * - no change if v is NULL or if k is not in v
 * - elements left in v are kept in order
 * - if k occurs several times, the last occurrence is removed
 */
extern void remove_index_from_vector(int32_t *v, int32_t k);


/*
 * Check whether k is present in v
 */
extern bool index_in_vector(int32_t *v, int32_t k);



#endif /* __INDEX_VECTORS_H */
