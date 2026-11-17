/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * VECTORS OF INTEGERS (RESIZABLE ARRAYS)
 */


#include "utils/memalloc.h"
#include "value_vector.h"

/*
 * Default initial size and max size
 */
#define DEF_VALUE_VECTOR_SIZE 10
#define MAX_VALUE_VECTOR_SIZE (UINT32_MAX/sizeof(mcsat_value_t))

/*
 * Integer vectors
 */
void init_value_vector(value_vector_t *v, uint32_t n) {
  if (n >= MAX_VALUE_VECTOR_SIZE) {
    out_of_memory();
  }
  v->capacity = n;
  v->size = 0;
  v->data = NULL;
  if (n > 0) {
    v->data = (mcsat_value_t*) safe_malloc(n * sizeof(mcsat_value_t));
  }
}

void delete_value_vector(value_vector_t *v) {
  uint32_t i;
  for (i = 0; i < v->size; ++ i) {
    mcsat_value_destruct(v->data + i);
  }
  safe_free(v->data);
  v->data = NULL;
}

void  extend_value_vector(value_vector_t *v) {
  uint32_t n;

  n = v->capacity;
  if (n == 0) {
    n = DEF_VALUE_VECTOR_SIZE;
  } else {
    n ++;
    n += n >> 1;
    if (n >= MAX_VALUE_VECTOR_SIZE) {
      out_of_memory();
    }
  }
  v->data = (mcsat_value_t *) safe_realloc(v->data, n * sizeof(mcsat_value_t));
  v->capacity = n;
}

void resize_value_vector(value_vector_t *v, uint32_t n) {
  if (n > v->capacity) {
    if (n >= MAX_VALUE_VECTOR_SIZE) {
      out_of_memory();
    }
    v->data = (mcsat_value_t *) safe_realloc(v->data, n * sizeof(mcsat_value_t));
    v->capacity = n;
  }
}

/*
 * Swap v1 and v2
 */
void value_vector_swap(value_vector_t *v1, value_vector_t *v2) {
  value_vector_t aux;

  aux = *v1;
  *v1 = *v2;
  *v2 = aux;
}

