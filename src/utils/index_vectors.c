/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * VECTORS OF INTEGERS
 */

/*
 * This used to be part of arith_vartable.  Moved it to a separate
 * file to share the code with other modules.
 */

#include "utils/index_vectors.h"


/*
 * Add index k at the end of vector *v
 * - if *v is NULL, allocate a fresh vector of default size
 */
void add_index_to_vector(int32_t **v, int32_t k) {
  index_vector_t *u;
  int32_t *d;
  uint32_t i, n;

  d = *v;
  if (d == NULL) {
    // initial allocation
    i = 0;
    n = DEF_IDX_VECTOR_SIZE;
    assert(n <= MAX_IDX_VECTOR_SIZE);
    u = (index_vector_t *) safe_malloc(sizeof(index_vector_t) + n * sizeof(int32_t));
    u->capacity = n;
    d = u->data;
    *v = d;
  } else {
    u = iv_header(d);
    i = u->size;
    n = u->capacity;
    if (i == n) {
      // make the vector 50% larger
      n ++;
      n += n>>1; // new capacity
      if (n > MAX_IDX_VECTOR_SIZE) {
        out_of_memory();
      }
      u = (index_vector_t *) safe_realloc(u, sizeof(index_vector_t) + n * sizeof(int32_t));
      u->capacity = n;
      d = u->data;
      *v = d;
    }
  }

  assert(i < u->capacity && d == u->data);
  d[i] = k;
  u->size = i+1;
}



/*
 * Make v large enough for n elements
 * - if *v is NULL, a fresh vector of size = max(n, default size) is allocated
 * - if *v is large enough, do nothing.
 */
void resize_index_vector(int32_t **v, uint32_t n) {
  index_vector_t *u;
  int32_t *d;
  uint32_t new_cap;

  d = *v;
  if (d == NULL) {
    new_cap = DEF_IDX_VECTOR_SIZE;
    if (new_cap < n) {
      new_cap = n;
      if (new_cap > MAX_IDX_VECTOR_SIZE) {
        out_of_memory();
      }
    }
    u = (index_vector_t *) safe_malloc(sizeof(index_vector_t) + new_cap * sizeof(int32_t));
    u->capacity = new_cap;
    u->size = 0;
    *v = u->data;
  } else {
    u = iv_header(d);
    if (u->capacity < n) {
      if (n > MAX_IDX_VECTOR_SIZE) {
        out_of_memory();
      }
      u = (index_vector_t *) safe_realloc(u, sizeof(index_vector_t) + n * sizeof(int32_t));
      u->capacity = n;
      *v = u->data;
    }
  }
}


/*
 * Create a vector that contains a[0 ... n-1]
 */
int32_t *make_index_vector(int32_t *a, uint32_t n) {
  index_vector_t *v;
  uint32_t i;

  if (n == 0) return NULL;
  if (n > MAX_IDX_VECTOR_SIZE) {
    out_of_memory();
  }
  v = (index_vector_t *) safe_malloc(sizeof(index_vector_t) + n * sizeof(int32_t));
  v->capacity = n;
  v->size = n;
  for (i=0; i<n; i++) {
    v->data[i] = a[i];
  }

  return v->data;
}


/*
 * Remove element k from vector v
 * - no change if v is NULL or if k is not in v
 */
void remove_index_from_vector(int32_t *v, int32_t k) {
  uint32_t i, n;

  if (v != NULL) {
    n = iv_size(v);
    /*
     * The common case should be when k is the last element of v
     */
    if (n > 0) {
      n --;
      if (v[n] != k) {
        i = n;
        do {
          if (i == 0) return; // k is not in v
          i --;
        } while (v[i] != k);
        // shift elements v[i+1... n] into v[i .. n-1]
        while (i < n) {
          v[i] = v[i+1];
          i ++;
        }
      }
      iv_header(v)->size = n;
    }
  }
}


/*
 * Remove v[i] from vector v
 */
void clear_index_elem(int32_t *v, uint32_t i) {
  uint32_t n;

  assert(v != NULL && i < iv_size(v));
  n = iv_size(v) - 1;
  // move last element into v[i] (no effect if i == n)
  v[i] = v[n];
  iv_header(v)->size = n;
}


/*
 * Check whether k is present in v
 */
bool index_in_vector(int32_t *v, int32_t k) {
  uint32_t i, n;

  if (v != NULL) {
    n = iv_size(v);
    for (i=0; i<n; i++) {
      if (v[i] == k) return true;
    }
  }
  return false;
}

