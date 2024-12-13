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
 * VECTORS OF INTEGERS (RESIZABLE ARRAYS)
 */


#include "utils/int_array_sort.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"

#include "mcsat/l2o/eval_vectors.h"

/*
 * Term_eval vectors
 */
void init_evector(evector_t *v, uint32_t n) {
  if (n >= MAX_IVECTOR_SIZE) {
    out_of_memory();
  }
  v->capacity = n;
  v->size = 0;
  v->data = NULL;
  if (n > 0) {
    v->data = (term_eval_t *) safe_malloc(n * sizeof(term_eval_t));
  }
}

void delete_evector(evector_t *v) {
  safe_free(v->data);
  v->data = NULL;
}

void extend_evector(evector_t *v) {
  uint32_t n;

  n = v->capacity;
  if (n == 0) {
    n = DEF_IVECTOR_SIZE;
  } else {
    n ++;
    n += n >> 1;
    if (n >= MAX_IVECTOR_SIZE) {
      out_of_memory();
    }
  }
  v->data = (term_eval_t *) safe_realloc(v->data, n * sizeof(term_eval_t));
  v->capacity = n;
}

void resize_evector(evector_t *v, uint32_t n) {
  if (n > v->capacity) {
    if (n >= MAX_IVECTOR_SIZE) {
      out_of_memory();
    }
    v->data = (term_eval_t *) safe_realloc(v->data, n * sizeof(term_eval_t));
    v->capacity = n;
  }
}

// copy array a into v. n = size of a
void evector_copy(evector_t *v, const term_eval_t *a, uint32_t n) {
  uint32_t i;

  resize_evector(v, n);
  for (i=0; i<n; i++) {
    v->data[i] = a[i];
  }
  v->size = n;
}


// add array a to v. n = size of a
void evector_add(evector_t *v, const term_eval_t *a, uint32_t n) {
  uint32_t i, m;

  m = v->size;
  resize_evector(v, n + m);
  for (i=0; i<n; i++) {
    v->data[m + i] = a[i];
  }
  v->size = n + m;
}


/*
 * Swap v1 and v2
 */
void evector_swap(evector_t *v1, evector_t *v2) {
  evector_t aux;

  aux = *v1;
  *v1 = *v2;
  *v2 = aux;
}



