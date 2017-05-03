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
 * VECTORS OF POINTERS
 */


#include "utils/memalloc.h"
#include "utils/ptr_vectors.h"



void init_pvector(pvector_t *v, uint32_t n) {
  if (n >= MAX_PVECTOR_SIZE) {
    out_of_memory();
  }
  v->capacity = n;
  v->size = 0;
  v->data = NULL;
  if (n > 0) {
    v->data = (void **) safe_malloc(n * sizeof(void *));
  }
}

void delete_pvector(pvector_t *v) {
  safe_free(v->data);
  v->data = NULL;
}

void extend_pvector(pvector_t *v) {
  uint32_t n;

  n = v->capacity;
  if (n == 0) {
    n = DEF_PVECTOR_SIZE;
  } else {
    n ++;
    n += n >> 1;
    if (n >= MAX_PVECTOR_SIZE) {
      out_of_memory();
    }
  }
  v->data = (void **) safe_realloc(v->data, n * sizeof(void *));
  v->capacity = n;
}

void resize_pvector(pvector_t *v, uint32_t n) {
  if (n > v->capacity) {
    if (n >= MAX_PVECTOR_SIZE) {
      out_of_memory();
    }
    v->data = (void **) safe_realloc(v->data, n * sizeof(void *));
    v->capacity = n;
  }
}


void pvector_copy(pvector_t *v, void **a, uint32_t n) {
  uint32_t i;

  resize_pvector(v, n);
  for (i=0; i<n; i++) {
    v->data[i] = a[i];
  }
  v->size = n;
}

