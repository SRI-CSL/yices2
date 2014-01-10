/*
 * BUFFER OPERATIONS
 */


#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

#include "memalloc.h"
#include "matrix_types.h"
#include "rationals.h"


/*************
 *  BUFFERS  *
 ************/

/*
 * Allocate and initialize a buffer of dimension n, 
 */
buffer_t *new_buffer(int n) {
  buffer_t *tmp;
  int i;

  tmp = (buffer_t *) safe_malloc(sizeof(buffer_t));
  tmp->dim = n;
  tmp->nelems = 0;
  tmp->active = (int *) safe_malloc(n * sizeof(int));
  tmp->q = (rat_t *) safe_malloc(n * sizeof(rat_t));
  tmp->tag = (mark_t *) safe_malloc(n * sizeof(mark_t));

  for (i=0; i<n; i++) {
    tmp->tag[i] = ZERO_COEFF;    
    rat_init(tmp->q + i);
  }

  return tmp;
}


/*
 * Set the dimension of buffer to n
 * - no effect if dimension is >= n
 * - otherwise buffer dimension is increased to n
 * The content of buffer is kept unchanged.
 */
void resize_buffer(buffer_t *buffer, int n) {
  int i, old_dim;

  old_dim = buffer->dim;
  if (n > old_dim) {
    buffer->dim = n;
    buffer->active = (int *) safe_realloc(buffer->active, n * sizeof(int));
    buffer->q = (rat_t *) safe_realloc(buffer->q, n * sizeof(rat_t));
    buffer->tag = (mark_t *) safe_realloc(buffer->tag, n * sizeof(mark_t));

    for (i=old_dim; i<n; i++) {
      buffer->tag[i] = ZERO_COEFF;
      rat_init(buffer->q + i);
    }
  }
  
}

/*
 * Delete buffer
 */
void delete_buffer(buffer_t *buffer) {
  int i, n;

  if (buffer != NULL) {
    n = buffer->dim;
    for (i=0; i<n; i++) {
      rat_clear(buffer->q + i);
    }
    safe_free(buffer->active);
    safe_free(buffer->q);
    safe_free(buffer->tag);  
    safe_free(buffer);
  }
}


/*
 * Normalize buffer:
 * - remove zero coefficients
 * - normalize the rationals
 */
void normalize_buffer(buffer_t *buffer) {
  int i, j, idx, n;
  rat_t *r;

  n = buffer->nelems;
  j = 0;
  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    r = buffer->q + idx;
    if (rat_is_zero(r)) {
      buffer->tag[idx] = ZERO_COEFF;
      rat_clear(r);
    } else {
      rat_normalize(r);
      buffer->active[j ++] = idx;
    }
  }
  buffer->nelems = j;
}




/*
 * Clear buffer: set all coeff to ZERO_COEFF
 */
void clear_buffer(buffer_t *buffer) {
  int i, idx, n;

  n = buffer->nelems;
  buffer->nelems = 0;
  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    buffer->tag[idx] = ZERO_COEFF;
    rat_clear(buffer->q + idx);
  }
}




/*
 * Permute content of buffer:
 * - buffer is updated as so that new_b[p[i]] := old_b[i]
 *   i.e., index i is mapped to p[i]
 * - aux buffer is modified and must be of size at least
 *   equal to buffer->nelems.
 */
void permute_buffer(buffer_t *buffer, int *p, rat_t *aux) {
  int i, idx, n;

  n = buffer->nelems;
  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    aux[i] = buffer->q[idx];
    buffer->tag[idx] = ZERO_COEFF;
    // Hack: set q[idx] to 0 (we cannot use rat_clear here)
    buffer->q[idx].num = 0;
    buffer->q[idx].den = 1;
  }

  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    idx = p[idx];
    buffer->active[i] = idx;
    buffer->tag[idx] = ACTIVE_COEFF;
    buffer->q[idx] = aux[i];
  }
}




/****************************************
 *  Set individual elements in a buffer *
 ***************************************/

void set_int_elem_in_buffer(buffer_t *buffer, int idx, int value) {
  int j;

  if (buffer->tag[idx] == ACTIVE_COEFF) {
    rat_clear(buffer->q + idx);
    rat_set_long(buffer->q + idx, value);
  } else {
    buffer->tag[idx] = ACTIVE_COEFF;
    rat_set_long(buffer->q + idx, value);
    j = buffer->nelems;
    buffer->active[j] = idx;
    buffer->nelems = j + 1;
  }
}


void set_mpq_elem_in_buffer(buffer_t *buffer, int idx, mpq_ptr value) {
  int j;

  if (buffer->tag[idx] == ACTIVE_COEFF) {
    rat_clear(buffer->q + idx);
    rat_set_mpq(buffer->q + idx, value);
  } else {
    buffer->tag[idx] = ACTIVE_COEFF;
    rat_set_mpq(buffer->q + idx, value);
    j = buffer->nelems;
    buffer->active[j] = idx;
    buffer->nelems = j + 1;
  }
}

void set_si_elem_in_buffer(buffer_t *buffer, int idx, long num, unsigned long den) {
  int j;

  if (buffer->tag[idx] == ACTIVE_COEFF) {
    rat_clear(buffer->q + idx);
    rat_set_si(buffer->q + idx, num, den);
  } else {
    buffer->tag[idx] = ACTIVE_COEFF;
    rat_set_si(buffer->q + idx, num, den);
    j = buffer->nelems;
    buffer->active[j] = idx;
    buffer->nelems = j + 1;
  }
}

void set_rat_elem_in_buffer(buffer_t *buffer, int idx, rat_t *value) {
  int j;

  if (buffer->tag[idx] == ACTIVE_COEFF) {
    rat_clear(buffer->q + idx);
    rat_set(buffer->q + idx, value);
  } else {
    buffer->tag[idx] = ACTIVE_COEFF;
    rat_set(buffer->q + idx, value);
    j = buffer->nelems;
    buffer->active[j] = idx;
    buffer->nelems = j + 1;
  }
}







/******************************
 *  COPY VECTORS IN BUFFERS   *
 *****************************/
/*
 * The buffer must be emptied before any copy.
 */

/*
 * Copy array of vector elements into buffer
 * n = number of elements in the array
 */
void copy_vectelem_in_buffer(buffer_t *buffer, vector_elem_t *v, int n) {
  int i, idx;

  buffer->nelems = n;
  for (i=0; i<n; i++) {
    idx = v[i].idx;
    buffer->active[i] = idx;
    buffer->tag[idx] = ACTIVE_COEFF;
    rat_set(buffer->q + idx, &v[i].coeff);    
  }
}


/*
 * Copy opposite of v into buffer
 * n = number of elements in the array
 */
void copy_opposite_vectelem_in_buffer(buffer_t *buffer, vector_elem_t *v, int n) {
  int i, idx;

  buffer->nelems = n;
  for (i=0; i<n; i++) {
    idx = v[i].idx;
    buffer->active[i] = idx;
    buffer->tag[idx] = ACTIVE_COEFF;
    rat_set_neg(buffer->q + idx, &v[i].coeff);
  }
}


/*
 * Copy vector v in buffer
 */
void copy_vector_in_buffer(buffer_t *buffer, vector_t *v) {
  copy_vectelem_in_buffer(buffer, v->data, v->size);
}


/*
 * Copy the opposite of vector v in buffer
 */
void copy_opposite_vector_in_buffer(buffer_t *buffer, vector_t *v) {
  copy_opposite_vectelem_in_buffer(buffer, v->data, v->size);
}


/*
 * Copy a matrix vector into buffer.
 */
void copy_mat_vector_in_buffer(buffer_t *buffer, mat_vector_t *v) {
  int i, j, idx, n;
  mat_elem_t *ve;

  n = v->size;
  j = 0;
  ve = v->data;
  for (i=0; i<n; i++) {
    idx = ve->idx;
    if (idx >= 0) {
      buffer->active[j++] = idx;
      buffer->tag[idx] = ACTIVE_COEFF;
      rat_set(buffer->q + idx, &ve->coeff);
    }
    ve ++;
  }
  buffer->nelems = j;
}


/*
 * Copy the opposite of a matrix vector into buffer.
 */
void copy_opposite_mat_vector_in_buffer(buffer_t *buffer, mat_vector_t *v) {
  int i, j, idx, n;

  n = v->size;
  j = 0;
  for (i=0; i<n; i++) {
    idx = v->data[i].idx;
    if (idx >= 0) {
      buffer->active[j++] = idx;
      buffer->tag[idx] = ACTIVE_COEFF;
      rat_set_neg(buffer->q + idx, &v->data[i].coeff);
    }    
  }
  buffer->nelems = j;
}





/***********************
 *  VECTOR OPERATIONS  *
 **********************/
/*
 * Operations: add/sub/addmul/submul
 * Argument can be: array of vector_elements (vector_elem_t)
 * vector or matrix_vector.
 */

/*
 * Add array of n vector_elements to buffer
 */
void add_vectelem_to_buffer(buffer_t *buffer, vector_elem_t *v, int n) {
  int i, idx, j;

  j = buffer->nelems;
  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (buffer->tag[idx] == ZERO_COEFF) {
      buffer->tag[idx] = ACTIVE_COEFF;
      buffer->active[j++] = idx;
      rat_set(buffer->q + idx, &v[i].coeff);
    } else {
      rat_add(buffer->q + idx, &v[i].coeff);
    }
  }
  buffer->nelems = j;
}

/*
 * Subtract array of n vector elements from buffer
 */
void sub_vectelem_from_buffer(buffer_t *buffer, vector_elem_t *v, int n) {
  int i, idx, j;

  j = buffer->nelems;
  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (buffer->tag[idx] == ZERO_COEFF) {
      buffer->tag[idx] = ACTIVE_COEFF;
      buffer->active[j++] = idx;
      rat_set_neg(buffer->q + idx, &v[i].coeff);
    } else {
      rat_sub(buffer->q + idx, &v[i].coeff);
    }
  }
  buffer->nelems = j;
}


/*
 * Add s * v to buffer where v is an array of n vector_elements
 */
void addmul_vectelem_to_buffer(buffer_t *buffer, vector_elem_t *v, int n, rat_t *s) {
  int i, idx, j;

  if (rat_is_one(s)) {
    add_vectelem_to_buffer(buffer, v, n);
    return;
  }

  if (rat_is_minus_one(s)) {
    sub_vectelem_from_buffer(buffer, v, n);
    return;
  }

  j = buffer->nelems;
  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (buffer->tag[idx] == ZERO_COEFF) {
      buffer->tag[idx] = ACTIVE_COEFF;
      buffer->active[j++] = idx;
      rat_set(buffer->q + idx, &v[i].coeff);
      rat_mul(buffer->q + idx, s);
    } else {
      rat_addmul(buffer->q + idx, &v[i].coeff, s);
    }
  }
  buffer->nelems = j;
}

/*
 * Subtract array of n vector elements from buffer
 */
void submul_vectelem_from_buffer(buffer_t *buffer, vector_elem_t *v, int n, rat_t *s) {
  int i, idx, j;

  if (rat_is_one(s)) {
    sub_vectelem_from_buffer(buffer, v, n);
    return;
  }

  if (rat_is_minus_one(s)) {
    add_vectelem_to_buffer(buffer, v, n);
    return;
  }

  j = buffer->nelems;
  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (buffer->tag[idx] == ZERO_COEFF) {
      buffer->tag[idx] = ACTIVE_COEFF;
      buffer->active[j++] = idx;
      rat_set_neg(buffer->q + idx, &v[i].coeff);
      rat_mul(buffer->q + idx, s);
    } else {
      rat_submul(buffer->q + idx, &v[i].coeff, s);
    }
  }
  buffer->nelems = j;
}




/*
 * Add vector to buffer
 */
void add_vector_to_buffer(buffer_t *buffer, vector_t *v) {
  add_vectelem_to_buffer(buffer, v->data, v->size);
}

/*
 * Subtract vector from buffer
 */
void sub_vector_from_buffer(buffer_t *buffer, vector_t *v) {
  sub_vectelem_from_buffer(buffer, v->data, v->size);
}


/*
 * Add s * vector to buffer for a rational s
 */
void addmul_vector_to_buffer(buffer_t *buffer, vector_t *v, rat_t *s) {
  addmul_vectelem_to_buffer(buffer, v->data, v->size, s);
}


/*
 * Subtract s * vector from buffer for a rational s
 */
void submul_vector_from_buffer(buffer_t *buffer, vector_t *v, rat_t *s) {
  submul_vectelem_from_buffer(buffer, v->data, v->size, s);
}




/*
 * Add matrix vector to buffer
 */
void add_mat_vector_to_buffer(buffer_t *buffer, mat_vector_t *v) {
  int i, j, n, idx;
  mat_elem_t *ve;

  n = v->size;
  ve = v->data;
  j = buffer->nelems;

  for (i=0; i<n; i++) {    
    idx = ve[i].idx;
    if (idx >= 0) {
      if (buffer->tag[idx] == ZERO_COEFF) {
	buffer->tag[idx] = ACTIVE_COEFF;
	buffer->active[j++] = idx;
	rat_set(buffer->q + idx, &ve[i].coeff);
      } else {
	rat_add(buffer->q + idx, &ve[i].coeff);
      }
    }
  }
  buffer->nelems = j;
}


/*
 * Subtract matrix vector from buffer
 */
void sub_mat_vector_from_buffer(buffer_t *buffer, mat_vector_t *v) {
  int i, j, n, idx;
  mat_elem_t *ve;

  n = v->size;
  ve = v->data;
  j = buffer->nelems;

  for (i=0; i<n; i++) {    
    idx = ve[i].idx;
    if (idx >= 0) {
      if (buffer->tag[idx] == ZERO_COEFF) {
	buffer->tag[idx] = ACTIVE_COEFF;
	buffer->active[j++] = idx;
	rat_set_neg(buffer->q + idx, &ve[i].coeff);
      } else {
	rat_sub(buffer->q + idx, &ve[i].coeff);
      }
    }
  }
  buffer->nelems = j;
}


/*
 * Add s * matrix-vector to buffer for a rational s
 */
void addmul_mat_vector_to_buffer(buffer_t *buffer, mat_vector_t *v, rat_t *s) {
  int i, j, n, idx;
  mat_elem_t *ve;

  if (rat_is_one(s)) {
    add_mat_vector_to_buffer(buffer, v);
    return;
  }

  if (rat_is_minus_one(s)) {
    sub_mat_vector_from_buffer(buffer, v);
    return;
  }

  n = v->size;
  ve = v->data;
  j = buffer->nelems;

  for (i=0; i<n; i++) {    
    idx = ve[i].idx;
    if (idx >= 0) {
      if (buffer->tag[idx] == ZERO_COEFF) {
	buffer->tag[idx] = ACTIVE_COEFF;
	buffer->active[j++] = idx;
	rat_set(buffer->q + idx, &ve[i].coeff);
	rat_mul(buffer->q + idx, s);
      } else {
	rat_addmul(buffer->q + idx, &ve[i].coeff, s);
      }
    }
  }
  buffer->nelems = j;  
}



/*
 * Subtract s * mat_vector from buffer for a rational s
 */
void submul_mat_vector_from_buffer(buffer_t *buffer, mat_vector_t *v, rat_t *s) {
  int i, j, n, idx;
  mat_elem_t *ve;

  if (s->den == 1) {
    if (s->num == 1) {
      sub_mat_vector_from_buffer(buffer, v);
      return;
    }
    if (s->num == -1) {
      add_mat_vector_to_buffer(buffer, v);
      return;
    }
  }

  n = v->size;
  ve = v->data;
  j = buffer->nelems;

  for (i=0; i<n; i++) {    
    idx = ve[i].idx;
    if (idx >= 0) {
      if (buffer->tag[idx] == ZERO_COEFF) {
	buffer->tag[idx] = ACTIVE_COEFF;
	buffer->active[j++] = idx;
	rat_set_neg(buffer->q + idx, &ve[i].coeff);
	rat_mul(buffer->q + idx, s);
      } else {
	rat_submul(buffer->q + idx, &ve[i].coeff, s);
      }
    }
  }
  buffer->nelems = j;
}




/*
 * OPERATIONS WITH ETA VECTOR
 */

/*
 * Construct product of buffer (interpreted as a column vector)
 * by the inverse of the elimeentary row matrix represented by k, v, n:
 * - k = row index for the eta-matrix
 * - v = vector of non-zero elements on row k 
 *       (except the diagonal element)
 *   n = size of v = number of non-zero elements
 *
 * This is done via:
 *   x[k] := x[k] - sum_{j=0}{n-1} x[v[j].idx] * v[j].coeff
 * where x[k] = buffer[k]
 */
void product_inv_eta(buffer_t *buffer, int k, vector_elem_t *v, int n) {
  int i, idx;
  rat_t *xk;

  xk = buffer->q + k;
  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (buffer->tag[idx] == ACTIVE_COEFF) {
      rat_submul(xk, buffer->q + idx, &v[i].coeff);
    }
  }
  if (rat_is_nonzero(xk) && buffer->tag[k] == ZERO_COEFF) {
    buffer->tag[k] = ACTIVE_COEFF;
    i = buffer->nelems;
    buffer->active[i] = k;
    buffer->nelems = i + 1;
  }
}



/*
 * OPERATION FOR SOLVING LINEAR EQUATIONS:
 * - one step of solving A x = b or x A = b where A is triangular
 *
 * Input: 
 *   - v = row or column vector of A
 *   - d_ptr = pointer to the diagonal element of v
 *     (i.e., v->data[d_ptr] is the diagonal element).
 *   - buffer contains vector b
 *
 * - for solving A x = b, v is a column vector of A 
 *   and b is a column vector
 * - for solving x A = b, v is a row vector of A
 *   and b is a row vector
 * 
 * Computation:
 * - let v_k = diagonal element of v
 * - replace b[k] by b'[k] = b[k] / v_k = x_k
 * - then for every i in column v: replace b[i]
 *   by b'[i] = b[i] - v_i * b'[k].
 *
 * Output:
 * - b' is stored in buffer
 * - v is unchanged
 */
void equa_solve_step(buffer_t *buffer, mat_vector_t *v, int d_ptr) {
  int i, j, k, n, idx;
  rat_t *bk;
  mat_elem_t *ve;

  // e = pointer to diagonal element of v
  ve = v->data + d_ptr;
  k = ve->idx;
  bk = buffer->q + k;

  // the function should be called only with bk non-zero
  // but just to be safe we check.
  if (buffer->tag[k] == ZERO_COEFF || rat_is_zero(bk)) {
    return; 
  }

  rat_div(bk, &ve->coeff); // b[k] := b[k] / v[k]

  // update the rest of buffer.
  n = v->size;
  ve = v->data;
  j = buffer->nelems;

  // special cases: bk = 1 or bk = -1
  if (rat_is_one(bk)) goto bk_is_one;
  if (rat_is_minus_one(bk)) goto bk_is_minus_one;

  for (i=0; i<n; i++) {
    idx = ve[i].idx;
    if (idx >= 0 && idx != k) {
      if (buffer->tag[idx] == ZERO_COEFF) {
	buffer->tag[idx] = ACTIVE_COEFF;
	buffer->active[j ++] = idx;
	rat_set_neg(buffer->q + idx, &ve[i].coeff);
	rat_mul(buffer->q + idx, bk);
      } else {
	rat_submul(buffer->q + idx, &ve[i].coeff, bk);
      }
    }
  }
  goto done;

  // special case: bk = 1
 bk_is_one:
  for (i=0; i<n; i++) {
    idx = ve[i].idx;
    if (idx >= 0 && idx != k) {
      if (buffer->tag[idx] == ZERO_COEFF) {
	buffer->tag[idx] = ACTIVE_COEFF;
	buffer->active[j ++] = idx;
	rat_set_neg(buffer->q + idx, &ve[i].coeff);
      } else {
	rat_sub(buffer->q + idx, &ve[i].coeff);
      }
    }
  }
  goto done;

  // special case: bk = -1
 bk_is_minus_one:
  for (i=0; i<n; i++) {
    idx = ve[i].idx;
    if (idx >= 0 && idx != k) {
      if (buffer->tag[idx] == ZERO_COEFF) {
	buffer->tag[idx] = ACTIVE_COEFF;
	buffer->active[j ++] = idx;
	rat_set(buffer->q + idx, &ve[i].coeff);
      } else {
	rat_add(buffer->q + idx, &ve[i].coeff);
      }
    }
  }

 done:
  buffer->nelems = j;
}
