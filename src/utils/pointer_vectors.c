/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * VECTORS OF POINTERS WITH HIDDEN HEADER
 */

#include <assert.h>

#include "utils/pointer_vectors.h"


/*
 * Add elem p at the end of vector *v
 * - if *v is NULL, allocate a fresh vector of default size
 */
void add_ptr_to_vector(void ***v, void *p) {
  ptr_vector_t *u;
  void **d;
  uint32_t i, n;

  d = *v;
  if (d == NULL) {
    // initial allocation
    n = DEF_PTR_VECTOR_SIZE;
    assert(n <= MAX_PTR_VECTOR_SIZE);
    u = (ptr_vector_t *) safe_malloc(sizeof(ptr_vector_t) + n * sizeof(void **));
    u->capacity = n;
    d = u->data;
    i = 0;
    *v = d;
  } else {
    u = pv_header(d);
    i = u->size;
    n = u->capacity;
    if (i == n) {
      // make v 50% larger
      n ++;
      n += n>>1;
      if (n > MAX_PTR_VECTOR_SIZE) {
        out_of_memory();
      }
      u = (ptr_vector_t *) safe_realloc(u, sizeof(ptr_vector_t) + n * sizeof(void *));
      u->capacity = n;
      d = u->data;
      *v = d;
    }
  }

  assert(i < u->capacity && d == u->data);
  d[i] = p;
  u->size = i+1;
}



/*
 * Make v large enough for at least n elements
 * - if *v is NULL, a fresh vector is allocate (size = max(n, default size))
 * - if *v is large enough, do nothing
 * Keep the size unchanged
 */
void resize_ptr_vector(void ***v, uint32_t n) {
  ptr_vector_t *u;
  void **d;
  uint32_t new_cap;

  d = *v;
  if (d == NULL) {
    new_cap = DEF_PTR_VECTOR_SIZE;
    if (new_cap < n) {
      new_cap = n;
      if (new_cap > MAX_PTR_VECTOR_SIZE) {
        out_of_memory();
      }
    }
    u = (ptr_vector_t *) safe_malloc(sizeof(ptr_vector_t) + new_cap * sizeof(void *));
    u->capacity = new_cap;
    u->size = 0;
    *v = u->data;
  } else {
    u = pv_header(d);
    if (u->capacity < n) {
      if (n > MAX_PTR_VECTOR_SIZE) {
        out_of_memory();
      }
      u = (ptr_vector_t *) safe_realloc(u, sizeof(ptr_vector_t) + n * sizeof(void *));
      u->capacity = n;
      *v = u->data;
    }
  }
}
