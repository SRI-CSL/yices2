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
 * VECTORS OF TERM_EVAL (RESIZABLE ARRAYS)
 */

#ifndef __EVAL_VECTORS_H
#define __EVAL_VECTORS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "mcsat/l2o/term_eval.h"

/*
 * Vector of term_eval elements
 * - capacity = size of the data array
 * - size = number of elements stored in data
 *   (i.e., the vector's content is data[0 ... size-1])
 */
typedef struct evector_s {
  uint32_t capacity;
  uint32_t size;
  term_eval_t *data;
} evector_t;


/*
 * Default initial size and max size
 */
#define DEF_IVECTOR_SIZE 10
#define MAX_IVECTOR_SIZE (UINT32_MAX/sizeof(int32_t))



/*
 * Initialize v with initial capacity = n
 * - v is empty
 */
extern void init_evector(evector_t *v, uint32_t n);

/*
 * Free the memory used by v
 */
extern void delete_evector(evector_t *v);

/*
 * Increase v's capacity by 50% (approximately)
 * Keep the content and size unchanged.
 */
extern void extend_evector(evector_t *v);

/*
 * Make v large enough for at least n elements
 * - increase the capacity if needed
 * - keep the content and size unchanged.
 */
extern void resize_evector(evector_t *v, uint32_t n);

/*
 * copy array a[0 .. n-1] into v
 */
extern void evector_copy(evector_t *v, const term_eval_t *a, uint32_t n);

/*
 * append a[0 .. n-1] to v
 */
extern void evector_add(evector_t *v, const term_eval_t *a, uint32_t n);


/*
 * Swap the content of v1 and v2
 */
extern void evector_swap(evector_t *v1, evector_t *v2);


/*
 * add x at the end of v
 */
static inline void evector_push(evector_t *v, term_eval_t x) {
  uint32_t i;

  i = v->size;
  if (i >= v->capacity) {
    extend_evector(v);
  }
  v->data[i] = x;
  v->size = i+1;
}

/*
 * get the last element
 */
static inline term_eval_t evector_last(evector_t *v) {
  assert(v->size > 0);
  return v->data[v->size - 1];
}

/*
 * remove the last element
 */
static inline void evector_pop(evector_t *v) {
  assert(v->size > 0);
  v->size --;
}

/*
 * combine pop and last: remove and return the last element
 */
static inline term_eval_t evector_pop2(evector_t *v) {
  assert(v->size > 0);
  v->size --;
  return v->data[v->size];
}

/*
 * Empty v
 */
static inline void evector_reset(evector_t *v) {
  v->size = 0;
}


/*
 * Keep the n first elements of v
 * - n must be less than or equal to v's current size.
 */
static inline void evector_shrink(evector_t *v, uint32_t n) {
  assert(n <= v->size);
  v->size = n;
}

#endif /* _EVAL__VECTORS_H */
