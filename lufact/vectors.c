/*
 * Operations on sparse vectors
 */


#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>
#include <limits.h>

#include "memalloc.h"
#include "matrix_types.h"
#include "rationals.h"


/******************************
 *  SPARSE VECTOR OPERATIONS  *
 *****************************/

/**
 * Create a new vector of initial capacity n
 * - n must be non-negative
 * - the vector is initially empty
 */
vector_t *new_vector(int n) {
  vector_t *tmp;

  tmp = (vector_t *) safe_malloc(sizeof(vector_t) + n * sizeof(vector_elem_t));
  tmp->capacity = n;
  tmp->size = 0;

  return tmp;
}


/**
 * Make *v large enough for at least n elements
 * - change the capacity, keep all elements already in v
 * - if *v is NULL, allocate a vector of capacity n
 */
void adjust_vector_capacity(vector_t **v, int n) {
  vector_t *vector;

  vector = *v;
  if (vector == NULL) {
    *v = new_vector(n);    
  } else if (vector->capacity < n) {
    vector = (vector_t *)
      safe_realloc(vector, sizeof(vector_t) + n * sizeof(vector_elem_t));

    vector->capacity = n;
    *v = vector;
  }
}


/**
 * Shrink *v so that its capacity equals its size
 */
void shrink_vector(vector_t **v) {
  vector_t *vector;
  int n;

  vector = *v;
  n = vector->size;
  if (n < vector->capacity) {
    vector = (vector_t *)
      safe_realloc(vector, sizeof(vector_t) + n * sizeof(vector_elem_t));
    vector->capacity = n;
    *v = vector;
  }
}


/*
 * - release all rational elements of v then delete v
 */
void cleanup_and_delete_vector(vector_t *v) {
  int i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    rat_clear(&v->data[i].coeff);
  }
  safe_free(v);
}


/**
 * Less safe version: just delete v.
 */
void delete_vector(vector_t *v) {
  safe_free(v);
}


/**
 * Release all rationals of v and empty vector v.
 */
void empty_vector(vector_t *v) {
  int i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    rat_clear(&v->data[i].coeff);
  }
  v->size = 0;
}




/**
 * Add element <i, a> at the end of vector *v
 * - resize *v if it's full
 * - allocate a new vector of default size if *v is NULL
 */
void add_int_elem_to_vector(vector_t **v, int i, int a) {
  int n, new_cap;
  vector_t *vector;

  vector = *v;
  if (vector == NULL) {
    n = 0;
    vector = new_vector(DEFAULT_VECTOR_SIZE);
    *v = vector;
  } else {
    n = vector->size;
    if (n == vector->capacity) {
      new_cap = n + (n >> 1) + 1;
      vector = (vector_t *)
	safe_realloc(vector, sizeof(vector_t) + new_cap * sizeof(vector_elem_t));
      vector->capacity = new_cap;
      *v = vector;
    }
  }

  vector->data[n].idx = i;
  rat_set_long(&vector->data[n].coeff, a);
  vector->size = n + 1;
}


/**
 * Add element <i, q> at the end of vector *v
 * - resize *v if it's full
 * - allocate a new vector of default size if *v is NULL
 */
void add_mpq_elem_to_vector(vector_t **v, int i, mpq_ptr q) {
  int n, new_cap;
  vector_t *vector;

  vector = *v;
  if (vector == NULL) {
    n = 0;
    vector = new_vector(DEFAULT_VECTOR_SIZE);
    *v = vector;
  } else {
    n = vector->size;
    if (n == vector->capacity) {
      new_cap = n + (n >> 1) + 1;
      vector = (vector_t *)
	safe_realloc(vector, sizeof(vector_t) + new_cap * sizeof(vector_elem_t));
      vector->capacity = new_cap;
      *v = vector;
    }
  }
  vector->data[n].idx = i;
  rat_set_mpq(&vector->data[n].coeff, q);
  vector->size = n + 1;
}


/**
 * Add element <i, num/den> at the end of *v.
 */
void add_si_elem_to_vector(vector_t **v, int i, long num, unsigned long den) {
  int n, new_cap;
  vector_t *vector;

  vector = *v;
  if (vector == NULL) {
    n = 0;
    vector = new_vector(DEFAULT_VECTOR_SIZE);
    *v = vector;
  } else {
    n = vector->size;
    if (n == vector->capacity) {
      new_cap = n + (n >> 1) + 1;
      vector = (vector_t *)
	safe_realloc(vector, sizeof(vector_t) + new_cap * sizeof(vector_elem_t));
      vector->capacity = new_cap;
      *v = vector;
    }
  }
  vector->data[n].idx = i;
  rat_set_si(&vector->data[n].coeff, num, den);
  vector->size = n + 1;  
}


/**
 * Add element <i, r> at the end of *v
 */
void add_rat_elem_to_vector(vector_t **v, int i, rat_t *r) {
  int n, new_cap;
  vector_t *vector;

  vector = *v;
  if (vector == NULL) {
    n = 0;
    vector = new_vector(DEFAULT_VECTOR_SIZE);
    *v = vector;
  } else {
    n = vector->size;
    if (n == vector->capacity) {
      new_cap = n + (n >> 1) + 1;
      vector = (vector_t *)
	safe_realloc(vector, sizeof(vector_t) + new_cap * sizeof(vector_elem_t));
      vector->capacity = new_cap;
      *v = vector;
    }
  }
  vector->data[n].idx = i;
  rat_set(&vector->data[n].coeff, r);
  vector->size = n + 1;
}


/**
 * Unsafe versions of the add operations: do not check for size.
 * - must be called with v initialized (v != NULL) and v->size < v->capacity.
 */
void fast_add_int_elem_to_vector(vector_t *v, int i, int a) {
  int n;

  n = v->size;
  v->data[n].idx = i;
  rat_set_long(&v->data[i].coeff, a);
  v->size = n + 1;
}

void fast_add_mpq_elem_to_vector(vector_t *v, int i, mpq_ptr q) {
  int n;

  n = v->size;
  v->data[n].idx = i;
  rat_set_mpq(&v->data[i].coeff, q);
  v->size = n + 1;
}

void fast_add_si_elem_to_vector(vector_t *v, int i, long num, unsigned long den) {
  int n;

  n = v->size;
  v->data[n].idx = i;
  rat_set_si(&v->data[i].coeff, num, den);
  v->size = n + 1;
}

void fast_add_rat_elem_to_vector(vector_t *v, int i, rat_t *r) {
  int n;

  n = v->size;
  v->data[n].idx = i;
  rat_set(&v->data[i].coeff, r);
  v->size = n + 1;
}


/*
 * Store buffer in vector.
 * Assumes buffer is normalized.
 */
void copy_buffer_in_vector(vector_t **v, buffer_t *buffer) {
  int i, n, idx;
  vector_t *vector;

  n = buffer->nelems;
  adjust_vector_capacity(v, n);
  vector = *v;

  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    vector->data[i].idx = idx;
    rat_set(&vector->data[i].coeff, buffer->q + idx);
  }

  // cleanup vector
  vector->size = n;
}


/*
 * Unsafe/faster version: must be called with v large enough
 * to store the buffer.
 */
void fast_copy_buffer_in_vector(vector_t *v, buffer_t *buffer) {
  int i, n, idx;

  n = buffer->nelems;
  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    v->data[i].idx = idx;
    rat_set(&v->data[i].coeff, buffer->q + idx);
  }

  // cleanup v
  v->size = n;
}
