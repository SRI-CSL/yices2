/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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

