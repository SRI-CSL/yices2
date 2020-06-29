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


/*
 * Integer vectors
 */
void init_ivector(ivector_t *v, uint32_t n) {
  if (n >= MAX_IVECTOR_SIZE) {
    out_of_memory();
  }
  v->capacity = n;
  v->size = 0;
  v->data = NULL;
  if (n > 0) {
    v->data = (int32_t *) safe_malloc(n * sizeof(int32_t));
  }
}

void delete_ivector(ivector_t *v) {
  safe_free(v->data);
  v->data = NULL;
}

void extend_ivector(ivector_t *v) {
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
  v->data = (int32_t *) safe_realloc(v->data, n * sizeof(int32_t));
  v->capacity = n;
}

void resize_ivector(ivector_t *v, uint32_t n) {
  if (n > v->capacity) {
    if (n >= MAX_IVECTOR_SIZE) {
      out_of_memory();
    }
    v->data = (int32_t *) safe_realloc(v->data, n * sizeof(int32_t));
    v->capacity = n;
  }
}

// copy array a into v. n = size of a
void ivector_copy(ivector_t *v, const int32_t *a, uint32_t n) {
  uint32_t i;

  resize_ivector(v, n);
  for (i=0; i<n; i++) {
    v->data[i] = a[i];
  }
  v->size = n;
}


// add array a to v. n = size of a
void ivector_add(ivector_t *v, const int32_t *a, uint32_t n) {
  int32_t *b;
  uint32_t i, m;

  m = v->size;
  resize_ivector(v, n + m);
  b = v->data + m;
  for (i=0; i<n; i++) {
    b[i] = a[i];
  }
  v->size = n + m;
}


/*
 * Swap v1 and v2
 */
void ivector_swap(ivector_t *v1, ivector_t *v2) {
  ivector_t aux;

  aux = *v1;
  *v1 = *v2;
  *v2 = aux;
}


/*
 * Sort and remove duplicates
 */
void ivector_remove_duplicates(ivector_t *v) {
  uint32_t n, i, j;
  int32_t x, y, *a;

  n = v->size;
  if (n >= 2) {
    a = v->data;
    int_array_sort(a, n);

    x = a[0];
    j = 1;
    for (i=1; i<n; i++) {
      y = a[i];
      if (x != y) {
        a[j] = y;
        x = y;
        j ++;
      }
    }
    v->size = j;
  }
}


