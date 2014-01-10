/*
 * Operations on sparse vectors and buffers
 */


#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>
#include <limits.h>

#include "memalloc.h"
#include "gmp_aux.h"
#include "matrix_types.h"



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


/**
 * Assuming all mpq elements of v are from the given bank
 * - release all mpq elements of v then delete v
 */
void cleanup_and_delete_vector(vector_t *v, mpq_bank_t *bank) {
  int i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    if (is_mpq_idx(v->data[i].idx)) {
      free_mpq(bank, v->data[i].coeff.q);
    }
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
 * Assuming all mpq elements of v are from the given bank,
 * - release all of them and empty vector v.
 */
void empty_vector(vector_t *v, mpq_bank_t *bank) {
  int i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    if (is_mpq_idx(v->data[i].idx)) {
      free_mpq(bank, v->data[i].coeff.q);
    }
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

  vector->data[n].idx = int_idx(i); // integer coefficient
  vector->data[n].coeff.a = a;
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
  vector->data[n].idx = mpq_idx(i); // mpq tag
  vector->data[n].coeff.q = q;
  vector->size = n + 1;
}



/**
 * Unsafe versions of the add operations: do not check for size.
 * - must be called with v initialized (v != NULL) and v->size < v->capacity.
 */
void fast_add_int_elem_to_vector(vector_t *v, int i, int a) {
  int n;

  n = v->size;
  v->data[n].idx = int_idx(i);
  v->data[n].coeff.a = a;
  v->size = n + 1;
}

void fast_add_mpq_elem_to_vector(vector_t *v, int i, mpq_ptr q) {
  int n;

  n = v->size;
  v->data[n].idx = mpq_idx(i);
  v->data[n].coeff.q = q;
  v->size = n + 1;
}




/*
 * Store buffer in vector and empty buffer.
 * Uses bank for allocating copies of mpq coefficients.
 * Assumes buffer is normalized.
 */
void copy_buffer_in_vector(vector_t **v, buffer_t *buffer, mpq_bank_t *bank) {
  int i, n, idx;
  vector_t *vector;
  mpq_ptr aux;

  n = buffer->nelems;
  adjust_vector_capacity(v, n);
  vector = *v;

  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    if (buffer->tag[idx] == MPQ_COEFF) {
      vector->data[i].idx = mpq_idx(idx); // mpq tagged index
      // copy buffer->q[idx] into vector[i]
      aux = get_mpq(bank);
      mpq_set(aux, buffer->q[idx]);
      vector->data[i].coeff.q = aux;
    } else {
      vector->data[i].idx = int_idx(idx); // integer bit = 1
      vector->data[i].coeff.a = buffer->a[idx];
    }
    buffer->tag[idx] = NO_COEFF;
  }

  // cleanup buffer
  buffer->nelems = 0;
  buffer->nops = 0;

  // cleanup vector
  vector->size = n;
}






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
  tmp->q = (mpq_t *) safe_malloc(n * sizeof(mpq_t));
  tmp->a = (int *) safe_malloc(n * sizeof(int));
  tmp->tag = (mark_t *) safe_malloc(n * sizeof(mark_t));
  mpq_init(tmp->r0);
  mpq_init(tmp->r1);
  tmp->nops = 0;

  for (i=0; i<n; i++) {
    tmp->tag[i] = NO_COEFF;    
    mpq_init(tmp->q[i]);
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
    buffer->q = (mpq_t *) safe_realloc(buffer->q, n * sizeof(mpq_t));
    buffer->a = (int *) safe_realloc(buffer->a, n * sizeof(int));
    buffer->tag = (mark_t *) safe_realloc(buffer->tag, n * sizeof(mark_t));

    for (i=old_dim; i<n; i++) {
      buffer->tag[i] = NO_COEFF;
      mpq_init(buffer->q[i]);
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
      mpq_clear(buffer->q[i]);
    }
    mpq_clear(buffer->r0);
    mpq_clear(buffer->r1);

    safe_free(buffer->active);
    safe_free(buffer->q);
    safe_free(buffer->a);
    safe_free(buffer->tag);  
    safe_free(buffer);
  }
}


/*
 * Normalize buffer:
 * - remove zero coefficients
 * - convert gmp coefficients that are integers
 *   and smaller in absolute value than NORMAL_CONST (or equal) 
 *   to integer coefficients
 * - convert integer coefficients that are larger in
 *   absolute value than NORMAL_CONST to gmp coefficients
 * - reset nops to 0
 */
void normalize_buffer(buffer_t *buffer) {
  int i, j, idx, n, a;
  mpq_ptr q;  

  n = buffer->nelems;
  j = 0;
  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    if (buffer->tag[idx] == MPQ_COEFF) {
      q = buffer->q[idx];
      if (mpq_sgn(q) == 0) {
	buffer->tag[idx] = NO_COEFF;
      } else {
	buffer->active[j++] = idx;
	if (mpq_is_normal_integer(q)) {
	  // Convert to an integer
	  buffer->tag[idx] = INT_COEFF;
	  buffer->a[idx] = mpq_get_si(q);
	}
      }
    } else {
      a = buffer->a[idx];
      if (a == 0) {
	buffer->tag[idx] = NO_COEFF;	
      } else {
	buffer->active[j++] = idx;
	if (abs(a) > (int) NORMAL_CONST) {
	  // Convert to an integer
	  buffer->tag[idx] = MPQ_COEFF;
	  mpq_set_from_int(buffer->q[idx], a);
	}
      }
    }    
  }
  buffer->nelems = j;
  buffer->nops = 0;
}




/*
 * Clear buffer: set all coeff to NO_COEFF
 */
void clear_buffer(buffer_t *buffer) {
  int i, idx, n;

  n = buffer->nelems;
  buffer->nelems = 0;
  buffer->nops = 0;
  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    buffer->tag[idx] = NO_COEFF;
  }
}







/**************************
 *   VECTOR OPERATIONS    *
 *************************/

/*
 * Convert integer coefficients that are larger than NORMAL_CONST 
 * to gmp numbers. Called whenever nops reaches 
 * NORMALIZATION_PERIOD to avoid overflows.
 */
static void renormalize_buffer(buffer_t *buffer) {
  int i, j, n, a;

  n = buffer->nelems;
  buffer->nops = 0;
  for (i=0; i<n; i++) {
    j = buffer->active[i];
    if (buffer->tag[j] == INT_COEFF) {
      a = buffer->a[j];
      if (abs(a) > (int) NORMAL_CONST) {
	buffer->tag[j] = MPQ_COEFF;
	mpq_set_from_int(buffer->q[j], a);
      }
    }
  }
}

static inline void prevent_overflow(buffer_t *buffer) {
  if (buffer->nops >= NORMALIZATION_PERIOD) {
    renormalize_buffer(buffer);
  }
}


/*
 * Copy array of vector elements into buffer
 * n = number of elements in the array
 */
void copy_vectelem_in_buffer(buffer_t *buffer, vector_elem_t *v, int n) {
  int i, idx;

  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (is_mpq_idx(idx)) {
      idx = untag_idx(idx);
      buffer->tag[idx] = MPQ_COEFF;
      mpq_set(buffer->q[idx], v[i].coeff.q);
    } else {
      idx = untag_idx(idx);
      buffer->tag[idx] = INT_COEFF;
      buffer->a[idx] = v[i].coeff.a;
    }
    buffer->active[i] = idx;
  }

  buffer->nelems = n;
  // force check for overflow on the next operation if any
  buffer->nops = NORMALIZATION_PERIOD;
}



/*
 * Copy opposite of v into buffer
 * n = number of elements in the array
 */
void copy_opposite_vectelem_in_buffer(buffer_t *buffer, vector_elem_t *v, int n) {
  int i, idx;

  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (is_mpq_idx(idx)) {
      idx = untag_idx(idx);
      buffer->tag[idx] = MPQ_COEFF;
      mpq_neg(buffer->q[idx], v[i].coeff.q);
    } else {
      idx = untag_idx(idx);
      buffer->tag[idx] = INT_COEFF;
      buffer->a[idx] = - v[i].coeff.a;
    }
    buffer->active[i] = idx;
  }

  buffer->nelems = n;  
  // force check for overflow on the next operation if any
  buffer->nops = NORMALIZATION_PERIOD;
}




/*
 * CASE 1: vector elements
 * - argument v given as an array of n vector_elemt_t structures
 * - v may contain integer and rational coefficients
 * - all integer coefficients in v must have absolute value <= NORMAL_CONST
 */

void add_vectelem_to_buffer(buffer_t *buffer, vector_elem_t *v, int n) {
  int i, idx, j, a;
  mpq_ptr aux, q;

  prevent_overflow(buffer);
  buffer->nops ++;

  j = buffer->nelems;
  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (is_mpq_idx(idx)) {
      q = v[i].coeff.q;
      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	mpq_set(buffer->q[idx], q);
	buffer->tag[idx] = MPQ_COEFF;
	buffer->active[j++] = idx;
	break;

      case MPQ_COEFF:
	aux = buffer->q[idx];
	mpq_add(aux, aux, q);
	break;

      case INT_COEFF:
	buffer->tag[idx] = MPQ_COEFF;
	aux = buffer->q[idx];
	mpq_set_from_int(aux, buffer->a[idx]);
	mpq_add(aux, aux, q);
	break;
      }
    } else {
      a = v[i].coeff.a;
      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	buffer->a[idx] = a;
	buffer->tag[idx] = INT_COEFF;
	buffer->active[j++] = idx;
	break;

      case MPQ_COEFF:
	mpq_set_from_int(buffer->r0, a);
	aux = buffer->q[idx];
	mpq_add(aux, aux, buffer->r0);
	break;

      case INT_COEFF:
	buffer->a[idx] += a;
	break;
      }
    }
  }

  buffer->nelems = j;
}


void sub_vectelem_from_buffer(buffer_t *buffer, vector_elem_t *v, int n) {
  int i, idx, j, a;
  mpq_ptr aux, q;

  prevent_overflow(buffer);
  buffer->nops ++;

  j = buffer->nelems;

  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (is_mpq_idx(idx)) {
      q = v[i].coeff.q;
      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	mpq_neg(buffer->q[idx], q);
	buffer->tag[idx] = MPQ_COEFF;
	buffer->active[j++] = idx;
	break;

      case MPQ_COEFF:
	aux = buffer->q[idx];
	mpq_sub(aux, aux, q);
	break;

      case INT_COEFF:
	buffer->tag[idx] = MPQ_COEFF;
	aux = buffer->q[idx];
	mpq_set_from_int(aux, buffer->a[idx]);
	mpq_sub(aux, aux, q);
	break;
      }
    } else {
      a = v[i].coeff.a;
      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	buffer->a[idx] = - a;
	buffer->tag[idx] = INT_COEFF;
	buffer->active[j++] = idx;
	break;

      case MPQ_COEFF:
	mpq_set_from_int(buffer->r0, a);
	aux = buffer->q[idx];
	mpq_sub(aux, aux, buffer->r0);
	break;

      case INT_COEFF:
	buffer->a[idx] -= a;
	break;
      }
    }
  }

  buffer->nelems = j;
}



/*
 * Add s * vector to buffer for a gmp number s
 * No integer overflow possible: any integer coefficient
 * modified is converted to a rational.
 */
void addmul_vectelem_to_buffer(buffer_t *buffer, vector_elem_t *v, int n, mpq_ptr s) {
  int i, idx, j;
  mpq_ptr aux, q;

  j = buffer->nelems;
  q = buffer->r0;

  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (is_mpq_idx(idx)) {
      mpq_mul(q, v[i].coeff.q, s);
    } else {
      mpq_set_from_int(q, v[i].coeff.a);
      mpq_mul(q, q, s);
    }

    idx = untag_idx(idx);
    switch (buffer->tag[idx]) {
    case NO_COEFF:
      mpq_set(buffer->q[idx], q);
      buffer->tag[idx] = MPQ_COEFF;
      buffer->active[j++] = idx;
      break;

    case MPQ_COEFF:
      aux = buffer->q[idx];
      mpq_add(aux, aux, q);
      break;

    case INT_COEFF:
      buffer->tag[idx] = MPQ_COEFF;
      aux = buffer->q[idx];
      mpq_set_from_int(aux, buffer->a[idx]);
      mpq_add(aux, aux, q);
      break;
    }
  }

  buffer->nelems = j;
}


/*
 * Subtract s * vector from buffer for a gmp number s
 * No integer overflow possible.
 */
void submul_vectelem_from_buffer(buffer_t *buffer, vector_elem_t *v, int n, mpq_ptr s) {
  int i, idx, j;
  mpq_ptr aux, q;

  j = buffer->nelems;
  q = buffer->r0;

  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (is_mpq_idx(idx)) {
      mpq_mul(q, v[i].coeff.q, s);
    } else {
      mpq_set_from_int(q, v[i].coeff.a);
      mpq_mul(q, q, s);
    }

    idx = untag_idx(idx);
    switch (buffer->tag[idx]) {
    case NO_COEFF:
      mpq_neg(buffer->q[idx], q);
      buffer->tag[idx] = MPQ_COEFF;
      buffer->active[j++] = idx;
      break;

    case MPQ_COEFF:
      aux = buffer->q[idx];
      mpq_sub(aux, aux, q);
      break;

    case INT_COEFF:
      buffer->tag[idx] = MPQ_COEFF;
      aux = buffer->q[idx];
      mpq_set_from_int(aux, buffer->a[idx]);
      mpq_sub(aux, aux, q);
      break;
    }
  }

  buffer->nelems = j;
}


/*
 * Add s * vector to buffer for an integer s.
 * Convert s to a gmp number and use addmul if |s| > MAX_FACTOR
 */
void addmuli_vectelem_to_buffer(buffer_t *buffer, vector_elem_t *v, int n, int s) {
  int i, idx, j, a;
  mpq_ptr aux, q;

  if (s == 1) {
    add_vectelem_to_buffer(buffer, v, n);
    return;
  }

  if (s == -1) {
    sub_vectelem_from_buffer(buffer, v, n);
    return;
  }

  if (abs(s) > MAX_FACTOR) {
    q = buffer->r1;
    mpq_set_from_int(q, s);
    addmul_vectelem_to_buffer(buffer, v, n, q);
    return;
  }

  prevent_overflow(buffer);
  buffer->nops ++;

  j = buffer->nelems;
  q = buffer->r0;

  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (is_mpq_idx(idx)) {
      mpq_set_from_int(q, s);
      mpq_mul(q, q, v[i].coeff.q);
      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	mpq_set(buffer->q[idx], q);
	buffer->tag[idx] = MPQ_COEFF;
	buffer->active[j++] = idx;
	break;

      case MPQ_COEFF:
	aux = buffer->q[idx];
	mpq_add(aux, aux, q);
	break;

      case INT_COEFF:
	buffer->tag[idx] = MPQ_COEFF;
	aux = buffer->q[idx];
	mpq_set_from_int(aux, buffer->a[idx]);
	mpq_add(aux, aux, q);
	break;
      }
    } else {
      a = v[i].coeff.a * s;
      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	buffer->a[idx] = a;
	buffer->tag[idx] = INT_COEFF;
	buffer->active[j++] = idx;
	break;

      case MPQ_COEFF:
	aux = buffer->q[idx];
	mpq_set_from_int(q, a);
	mpq_add(aux, aux, q);
	break;

      case INT_COEFF:
	buffer->a[idx] += a;
	break;
      }
    }
  }

  buffer->nelems = j;
}



/*
 * Subtract s * vector from buffer for an integer s.
 * Convert s to a gmp number if |s| > MAX_FACTOR.
 */
void submuli_vectelem_from_buffer(buffer_t *buffer, vector_elem_t *v, int n, int s) {
  int i, idx, j, a;
  mpq_ptr aux, q;

  if (s == -1) {
    add_vectelem_to_buffer(buffer, v, n);
    return;
  }

  if (s == 1) {
    sub_vectelem_from_buffer(buffer, v, n);
    return;
  }

  if (abs(s) > MAX_FACTOR) {
    q = buffer->r1;
    mpq_set_from_int(q, s);
    submul_vectelem_from_buffer(buffer, v, n, q);
    return;
  }

  prevent_overflow(buffer);
  buffer->nops ++;

  j = buffer->nelems;
  q = buffer->r0;

  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (is_mpq_idx(idx)) {
      mpq_set_from_int(q, s);
      mpq_mul(q, q, v[i].coeff.q);
      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	mpq_neg(buffer->q[idx], q);
	buffer->tag[idx] = MPQ_COEFF;
	buffer->active[j++] = idx;
	break;

      case MPQ_COEFF:
	aux = buffer->q[idx];
	mpq_sub(aux, aux, q);
	break;

      case INT_COEFF:
	buffer->tag[idx] = MPQ_COEFF;
	aux = buffer->q[idx];
	mpq_set_from_int(aux, buffer->a[idx]);
	mpq_sub(aux, aux, q);
	break;
      }
    } else {
      a = v[i].coeff.a * s;
      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	buffer->a[idx] = - a;
	buffer->tag[idx] = INT_COEFF;
	buffer->active[j++] = idx;
	break;

      case MPQ_COEFF:
	aux = buffer->q[idx];
	mpq_set_from_int(q, a);
	mpq_sub(aux, aux, q);
	break;

      case INT_COEFF:
	buffer->a[idx] -= a;
	break;
      }
    }
  }

  buffer->nelems = j;
}








/*
 * CASE 2: integer-only vector elements
 * - argument v given as an array of vector elements
 * - v contains only integer
 * - all integer coefficients in v must have absolute value <= NORMAL_CONST
 */

void add_int_vectelem_to_buffer(buffer_t *buffer, vector_elem_t *v, int n) {
  int i, idx, j, a;
  mpq_ptr aux;

  prevent_overflow(buffer);
  buffer->nops ++;

  j = buffer->nelems;
  for (i=0; i<n; i++) {
    idx = untag_idx(v[i].idx);
    a = v[i].coeff.a;
    switch (buffer->tag[idx]) {
    case NO_COEFF:
      buffer->a[idx] = a;
      buffer->tag[idx] = INT_COEFF;
      buffer->active[j++] = idx;
      break;

    case MPQ_COEFF:
      mpq_set_from_int(buffer->r0, a);
      aux = buffer->q[idx];
      mpq_add(aux, aux, buffer->r0);
      break;

    case INT_COEFF:
      buffer->a[idx] += a;
      break;
    }
  }

  buffer->nelems = j;
}


void sub_int_vectelem_from_buffer(buffer_t *buffer, vector_elem_t *v, int n) {
  int i, idx, j, a;
  mpq_ptr aux;

  prevent_overflow(buffer);
  buffer->nops ++;

  j = buffer->nelems;

  for (i=0; i<n; i++) {
    idx = untag_idx(v[i].idx);
    a = v[i].coeff.a;
    switch (buffer->tag[idx]) {
    case NO_COEFF:
      buffer->a[idx] = - a;
      buffer->tag[idx] = INT_COEFF;
      buffer->active[j++] = idx;
      break;

    case MPQ_COEFF:
      mpq_set_from_int(buffer->r0, a);
      aux = buffer->q[idx];
      mpq_sub(aux, aux, buffer->r0);
      break;

    case INT_COEFF:
      buffer->a[idx] -= a;
      break;
    }
  }

  buffer->nelems = j;
}


/*
 * Add s * vector to buffer for a gmp number s
 * No integer overflow possible.
 */
void addmul_int_vectelem_to_buffer(buffer_t *buffer, vector_elem_t *v, int n, mpq_ptr s) {
  int i, idx, j;
  mpq_ptr aux, q;

  j = buffer->nelems;
  q = buffer->r0;

  for (i=0; i<n; i++) {
    idx = untag_idx(v[i].idx);
    mpq_set_from_int(q, v[i].coeff.a);
    mpq_mul(q, q, s);

    switch (buffer->tag[idx]) {
    case NO_COEFF:
      mpq_set(buffer->q[idx], q);
      buffer->tag[idx] = MPQ_COEFF;
      buffer->active[j++] = idx;
      break;

    case MPQ_COEFF:
      aux = buffer->q[idx];
      mpq_add(aux, aux, q);
      break;

    case INT_COEFF:
      buffer->tag[idx] = MPQ_COEFF;
      aux = buffer->q[idx];
      mpq_set_from_int(aux, buffer->a[idx]);
      mpq_add(aux, aux, q);
      break;
    }
  }

  buffer->nelems = j;
}



/*
 * Subtract s * vector from buffer for a gmp number s
 * No integer overflow possible.
 */
void submul_int_vectelem_from_buffer(buffer_t *buffer, vector_elem_t *v, int n, mpq_ptr s) {
  int i, idx, j;
  mpq_ptr aux, q;

  j = buffer->nelems;
  q = buffer->r0;

  for (i=0; i<n; i++) {
    idx = untag_idx(v[i].idx);
    mpq_set_from_int(q, v[i].coeff.a);
    mpq_mul(q, q, s);

    switch (buffer->tag[idx]) {
    case NO_COEFF:
      mpq_neg(buffer->q[idx], q);
      buffer->tag[idx] = MPQ_COEFF;
      buffer->active[j++] = idx;
      break;

    case MPQ_COEFF:
      aux = buffer->q[idx];
      mpq_sub(aux, aux, q);
      break;

    case INT_COEFF:
      buffer->tag[idx] = MPQ_COEFF;
      aux = buffer->q[idx];
      mpq_set_from_int(aux, buffer->a[idx]);
      mpq_sub(aux, aux, q);
      break;
    }
  }

  buffer->nelems = j;
}




/*
 * Add s * vector to buffer for an integer  s
 * Convert s to an mpq number and use addmul if |s| > MAX_FACTOR.
 */
void addmuli_int_vectelem_to_buffer(buffer_t *buffer, vector_elem_t *v, int n, int s) {
  int i, idx, j, a;
  mpq_ptr aux;

  if (s == 1) {
    add_int_vectelem_to_buffer(buffer, v, n);
    return;
  }

  if (s == -1) {
    sub_int_vectelem_from_buffer(buffer, v, n);
    return;
  }

  if (abs(s) > MAX_FACTOR) {
    aux = buffer->r1;
    mpq_set_from_int(aux, s);
    addmul_int_vectelem_to_buffer(buffer, v, n, aux);
    return;
  }

  prevent_overflow(buffer);
  buffer->nops ++;

  j = buffer->nelems;

  for (i=0; i<n; i++) {
    idx = untag_idx(v[i].idx);
    a = s * v[i].coeff.a;
    switch (buffer->tag[idx]) {
    case NO_COEFF:
      buffer->a[idx] = a;
      buffer->tag[idx] = INT_COEFF;
      buffer->active[j++] = idx;
      break;

    case MPQ_COEFF:
      mpq_set_from_int(buffer->r0, a);
      aux = buffer->q[idx];
      mpq_add(aux, aux, buffer->r0);
      break;

    case INT_COEFF:
      buffer->a[idx] += a;
      break;
    }
  }

  buffer->nelems = j;
}



/*
 * Subtract s * vector from buffer for an integer  s
 * Convert s to an mpq number if |s| > MAX_FACTOR.
 */
void submuli_int_vectelem_from_buffer(buffer_t *buffer, vector_elem_t *v, int n, int s) {
  int i, idx, j, a;
  mpq_ptr aux;

  if (s == -1) {
    add_int_vectelem_to_buffer(buffer, v, n);
    return;
  }

  if (s == 1) {
    sub_int_vectelem_from_buffer(buffer, v, n);
    return;
  }

  if (abs(s) > MAX_FACTOR) {
    aux = buffer->r1;
    mpq_set_from_int(aux, s);
    submul_int_vectelem_from_buffer(buffer, v, n, aux);
    return;
  }

  prevent_overflow(buffer);
  buffer->nops ++;

  j = buffer->nelems;

  for (i=0; i<n; i++) {
    idx = untag_idx(v[i].idx);
    a = s * v[i].coeff.a;
    switch (buffer->tag[idx]) {
    case NO_COEFF:
      buffer->a[idx] = - a;
      buffer->tag[idx] = INT_COEFF;
      buffer->active[j++] = idx;
      break;

    case MPQ_COEFF:
      mpq_set_from_int(buffer->r0, a);
      aux = buffer->q[idx];
      mpq_sub(aux, aux, buffer->r0);
      break;

    case INT_COEFF:
      buffer->a[idx] -= a;
      break;
    }
  }

  buffer->nelems = j;
}








/*
 * CASE 3: argument is given as a vector_t object
 */

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
 * Add s * vector to buffer for a gmp number s
 */
void addmul_vector_to_buffer(buffer_t *buffer, vector_t *v, mpq_ptr s) {
  addmul_vectelem_to_buffer(buffer, v->data, v->size, s);
}


/*
 * Subtract s * vector from buffer for a gmp number s
 */
void submul_vector_from_buffer(buffer_t *buffer, vector_t *v, mpq_ptr s) {
  submul_vectelem_from_buffer(buffer, v->data, v->size, s);
}


/*
 * Add s * vector to buffer for an integer s
 */
void addmuli_vector_to_buffer(buffer_t *buffer, vector_t *v, int s) {
  addmuli_vectelem_to_buffer(buffer, v->data, v->size, s);
}


/*
 * Subtract s * vector from buffer for an integer s
 */
void submuli_vector_from_buffer(buffer_t *buffer, vector_t *v, int s) {
  submuli_vectelem_from_buffer(buffer, v->data, v->size, s);
}





/**************************************
 * CASE 4: Argument is a row-vector   *
 *************************************/

/*
 * Copy a row vector into buffer.
 */
void copy_row_vector_in_buffer(buffer_t *buffer, row_vector_t *v) {
  int i, j, n, idx;
  row_elem_t *ve;

  n = v->size;
  ve = v->data;
  j = 0;
  for (i=0; i<n; i++) {
    idx = ve[i].c_idx;
    if (idx >= 0) {
      if (is_mpq_idx(idx)) {
	idx = untag_idx(idx);
	buffer->tag[idx] = MPQ_COEFF;
	mpq_set(buffer->q[idx], ve[i].coeff.q);
      } else {
	idx = untag_idx(idx);
	buffer->tag[idx] = INT_COEFF;
	buffer->a[idx] = ve[i].coeff.a;
      }
      buffer->active[j++] = idx;
    }
  }
  buffer->nelems = j;
  buffer->nops = 1;
  // force check for overflow on the next operation if any
  //  buffer->nops = NORMALIZATION_PERIOD;
}



/*
 * Copy the opposite of vector v in buffer
 */
void copy_opposite_row_vector_in_buffer(buffer_t *buffer, row_vector_t *v) {
  int i, j, n, idx;
  row_elem_t *ve;

  n = v->size;
  ve = v->data;
  j = 0;
  for (i=0; i<n; i++) {
    idx = ve[i].c_idx;
    if (idx >= 0) {
      if (is_mpq_idx(idx)) {
	idx = untag_idx(idx);
	buffer->tag[idx] = MPQ_COEFF;
	mpq_neg(buffer->q[idx], ve[i].coeff.q);
      } else {
	idx = untag_idx(idx);
	buffer->tag[idx] = INT_COEFF;
	buffer->a[idx] = - ve[i].coeff.a;
      }
      buffer->active[j++] = idx;
    }
  }

  buffer->nelems = j;
  buffer->nops = 1;
  // force check for overflow on the next operation if any
  //  buffer->nops = NORMALIZATION_PERIOD;
}




/*
 * Add row vector to buffer
 */
void add_row_vector_to_buffer(buffer_t *buffer, row_vector_t *v) {
  int i, n, idx, j, a;
  row_elem_t *ve;
  mpq_ptr aux, q;

  prevent_overflow(buffer);
  buffer->nops ++;

  n = v->size;
  ve = v->data;
  j = buffer->nelems;

  for (i=0; i<n; i++) {    
    idx = ve[i].c_idx;
    if (idx >= 0) {
      if (is_mpq_idx(idx)) {
	q = ve[i].coeff.q;
	idx = untag_idx(idx);
	switch (buffer->tag[idx]) {
	case NO_COEFF:
	  mpq_set(buffer->q[idx], q);
	  buffer->tag[idx] = MPQ_COEFF;
	  buffer->active[j++] = idx;
	  break;

	case MPQ_COEFF:
	  aux = buffer->q[idx];
	  mpq_add(aux, aux, q);
	  break;

	case INT_COEFF:
	  buffer->tag[idx] = MPQ_COEFF;
	  aux = buffer->q[idx];
	  mpq_set_from_int(aux, buffer->a[idx]);
	  mpq_add(aux, aux, q);
	  break;
	}
      } else {
	a = ve[i].coeff.a;
	idx = untag_idx(idx);
	switch (buffer->tag[idx]) {
	case NO_COEFF:
	  buffer->a[idx] = a;
	  buffer->tag[idx] = INT_COEFF;
	  buffer->active[j++] = idx;
	  break;

	case MPQ_COEFF:
	  mpq_set_from_int(buffer->r0, a);
	  aux = buffer->q[idx];
	  mpq_add(aux, aux, buffer->r0);
	  break;

	case INT_COEFF:
	  buffer->a[idx] += a;
	  break;
	}
      }
    }
  }
  buffer->nelems = j;
}


/*
 * Subtract row vector from buffer
 */
void sub_row_vector_from_buffer(buffer_t *buffer, row_vector_t *v) {
  int i, n, idx, j, a;
  row_elem_t *ve;
  mpq_ptr aux, q;

  prevent_overflow(buffer);
  buffer->nops ++;

  n = v->size;
  ve = v->data;
  j = buffer->nelems;

  for (i=0; i<n; i++) {
    idx = ve[i].c_idx;
    if (idx >= 0) {
      if (is_mpq_idx(idx)) {
	q = ve[i].coeff.q;
	idx = untag_idx(idx);
	switch (buffer->tag[idx]) {
	case NO_COEFF:
	  mpq_neg(buffer->q[idx], q);
	  buffer->tag[idx] = MPQ_COEFF;
	  buffer->active[j++] = idx;
	  break;

	case MPQ_COEFF:
	  aux = buffer->q[idx];
	  mpq_sub(aux, aux, q);
	  break;

	case INT_COEFF:
	  buffer->tag[idx] = MPQ_COEFF;
	  aux = buffer->q[idx];
	  mpq_set_from_int(aux, buffer->a[idx]);
	  mpq_sub(aux, aux, q);
	  break;
	}
      } else {
	a = ve[i].coeff.a;
	idx = untag_idx(idx);
	switch (buffer->tag[idx]) {
	case NO_COEFF:
	  buffer->a[idx] = - a;
	  buffer->tag[idx] = INT_COEFF;
	  buffer->active[j++] = idx;
	  break;

	case MPQ_COEFF:
	  mpq_set_from_int(buffer->r0, a);
	  aux = buffer->q[idx];
	  mpq_sub(aux, aux, buffer->r0);
	  break;

	case INT_COEFF:
	  buffer->a[idx] -= a;
	  break;
	}
      }
    }
  }

  buffer->nelems = j;
}


/*
 * Add s * row-vector to buffer for a gmp number s
 * No integer overflow possible.
 */
void addmul_row_vector_to_buffer(buffer_t *buffer, row_vector_t *v, mpq_ptr s) {
  int i, n, idx, j;
  row_elem_t *ve;
  mpq_ptr aux, q;

  n = v->size;
  ve = v->data;
  j = buffer->nelems;
  q = buffer->r0;

  for (i=0; i<n; i++) {
    idx = ve[i].c_idx;
    if (idx >= 0) {
      if (is_mpq_idx(idx)) {
	mpq_mul(q, ve[i].coeff.q, s);
      } else {
	mpq_set_from_int(q, ve[i].coeff.a);
	mpq_mul(q, q, s);
      }

      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	mpq_set(buffer->q[idx], q);
	buffer->tag[idx] = MPQ_COEFF;
	buffer->active[j++] = idx;
	break;

      case MPQ_COEFF:
	aux = buffer->q[idx];
	mpq_add(aux, aux, q);
	break;

      case INT_COEFF:
	buffer->tag[idx] = MPQ_COEFF;
	aux = buffer->q[idx];
	mpq_set_from_int(aux, buffer->a[idx]);
	mpq_add(aux, aux, q);
	break;
      }
    }
  }

  buffer->nelems = j;
}



/*
 * Add s * vector to buffer for an integer s.
 * Convert s to a gmp number and use addmul if |s| > MAX_FACTOR
 */
void addmuli_row_vector_to_buffer(buffer_t *buffer, row_vector_t *v, int s) {
  int i, n, idx, j, a;
  row_elem_t *ve;
  mpq_ptr aux, q;

  if (s == 1) {
    add_row_vector_to_buffer(buffer, v);
    return;
  }

  if (s == -1) {
    sub_row_vector_from_buffer(buffer, v);
    return;
  }

  if (abs(s) > MAX_FACTOR) {
    q = buffer->r1;
    mpq_set_from_int(q, s);
    addmul_row_vector_to_buffer(buffer, v, q);
    return;
  }

  prevent_overflow(buffer);
  buffer->nops ++;

  n = v->size;
  ve = v->data;
  j = buffer->nelems;
  q = buffer->r0;

  for (i=0; i<n; i++) {
    idx = ve[i].c_idx;
    if (idx >= 0) {
      if (is_mpq_idx(idx)) {
	mpq_set_from_int(q, s);
	mpq_mul(q, q, ve[i].coeff.q);
	idx = untag_idx(idx);
	switch (buffer->tag[idx]) {
	case NO_COEFF:
	  mpq_set(buffer->q[idx], q);
	  buffer->tag[idx] = MPQ_COEFF;
	  buffer->active[j++] = idx;
	  break;

	case MPQ_COEFF:
	  aux = buffer->q[idx];
	  mpq_add(aux, aux, q);
	  break;

	case INT_COEFF:
	  buffer->tag[idx] = MPQ_COEFF;
	  aux = buffer->q[idx];
	  mpq_set_from_int(aux, buffer->a[idx]);
	  mpq_add(aux, aux, q);
	  break;
	}
      } else {
	a = ve[i].coeff.a * s;
	idx = untag_idx(idx);
	switch (buffer->tag[idx]) {
	case NO_COEFF:
	  buffer->a[idx] = a;
	  buffer->tag[idx] = INT_COEFF;
	  buffer->active[j++] = idx;
	  break;

	case MPQ_COEFF:
	  aux = buffer->q[idx];
	  mpq_set_from_int(q, a);
	  mpq_add(aux, aux, q);
	  break;

	case INT_COEFF:
	  buffer->a[idx] += a;
	  break;
	}
      }
    }
  }

  buffer->nelems = j;
}



/*
 * Subtract s * row_vector from buffer for a gmp number s
 * No integer overflow possible.
 */
void submul_row_vector_from_buffer(buffer_t *buffer, row_vector_t *v, mpq_ptr s) {
  int i, n, idx, j;
  row_elem_t *ve;
  mpq_ptr aux, q;

  n = v->size;
  ve = v->data;
  j = buffer->nelems;
  q = buffer->r0;

  for (i=0; i<n; i++) {
    idx = ve[i].c_idx;
    if (idx >= 0) {
      if (is_mpq_idx(idx)) {
	mpq_mul(q, ve[i].coeff.q, s);
      } else {
	mpq_set_from_int(q, ve[i].coeff.a);
	mpq_mul(q, q, s);
      }

      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	mpq_neg(buffer->q[idx], q);
	buffer->tag[idx] = MPQ_COEFF;
	buffer->active[j++] = idx;
	break;

      case MPQ_COEFF:
	aux = buffer->q[idx];
	mpq_sub(aux, aux, q);
	break;

      case INT_COEFF:
	buffer->tag[idx] = MPQ_COEFF;
	aux = buffer->q[idx];
	mpq_set_from_int(aux, buffer->a[idx]);
	mpq_sub(aux, aux, q);
	break;
      }
    }
  }

  buffer->nelems = j;
}


/*
 * Subtract s * row-vector from buffer for an integer s.
 * Convert s to a gmp number if |s| > MAX_FACTOR.
 */
void submuli_row_vector_from_buffer(buffer_t *buffer, row_vector_t *v, int s) {
  int i, n, idx, j, a;
  row_elem_t *ve;
  mpq_ptr aux, q;

  if (s == -1) {
    add_row_vector_to_buffer(buffer, v);
    return;
  }

  if (s == 1) {
    sub_row_vector_from_buffer(buffer, v);
    return;
  }

  if (abs(s) > MAX_FACTOR) {
    q = buffer->r1;
    mpq_set_from_int(q, s);
    submul_row_vector_from_buffer(buffer, v, q);
    return;
  }

  prevent_overflow(buffer);
  buffer->nops ++;

  n = v->size;
  ve = v->data;
  j = buffer->nelems;
  q = buffer->r0;

  for (i=0; i<n; i++) {
    idx = ve[i].c_idx;
    if (idx >= 0) {
      if (is_mpq_idx(idx)) {
	mpq_set_from_int(q, s);
	mpq_mul(q, q, ve[i].coeff.q);
	idx = untag_idx(idx);
	switch (buffer->tag[idx]) {
	case NO_COEFF:
	  mpq_neg(buffer->q[idx], q);
	  buffer->tag[idx] = MPQ_COEFF;
	  buffer->active[j++] = idx;
	  break;

	case MPQ_COEFF:
	  aux = buffer->q[idx];
	  mpq_sub(aux, aux, q);
	  break;

	case INT_COEFF:
	  buffer->tag[idx] = MPQ_COEFF;
	  aux = buffer->q[idx];
	  mpq_set_from_int(aux, buffer->a[idx]);
	  mpq_sub(aux, aux, q);
	  break;
	}
      } else {
	a = ve[i].coeff.a * s;
	idx = untag_idx(idx);
	switch (buffer->tag[idx]) {
	case NO_COEFF:
	  buffer->a[idx] = - a;
	  buffer->tag[idx] = INT_COEFF;
	  buffer->active[j++] = idx;
	  break;

	case MPQ_COEFF:
	  aux = buffer->q[idx];
	  mpq_set_from_int(q, a);
	  mpq_sub(aux, aux, q);
	  break;

	case INT_COEFF:
	  buffer->a[idx] -= a;
	  break;
	}
      }
    }
  }

  buffer->nelems = j;
}




/*
 * OPERATIONS WITH ETA VECTOR
 */

/*
 * Construct product of buffer (interpreted as a row vector)
 * by the inverse of the eta-matrix represented by k, v, n:
 * - k = column index for the eta-matrix
 * - v = vector of non-zero elements on column k 
 *       (except the diagonal element)
 *   n = size of v = number of non-zero elements
 *
 * This is done via:
 *   x[k] := x[k] - sum_{j=0}{n-1} x[v[j].idx] * v[j].coeff
 * where x[k] = buffer[k]
 */
void product_inv_eta(buffer_t *buffer, int k, vector_elem_t *v, int n) {
  int i, idx;
  mpq_ptr qr, aux;
  int ar, prod;

  /*
   * The loop below compute x[k] using qr and ar:
   * at the end of the loop, new coefficient = qr + ar
   */
  qr = buffer->q[k];
  ar = 0;
  switch (buffer->tag[k]) {
  case NO_COEFF:
    mpq_set_from_int(qr, 0);
    break;

  case MPQ_COEFF:
    break;

  case INT_COEFF:
    mpq_set_from_int(qr, 0);
    ar = buffer->a[k];
    break;
  }

  aux = buffer->r0;

  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (is_mpq_idx(idx)) {
      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	break;

      case MPQ_COEFF:
	// qr := qr - buffer->q[idx] * v[i].coeff.q
	mpq_set(aux, buffer->q[idx]);
	mpq_mul(aux, aux, v[i].coeff.q);
	mpq_sub(qr, qr, aux);
	break;

      case INT_COEFF:
	// qr := qr - buffer->q[idx] * v[i].coeff.q
	mpq_set_from_int(aux, buffer->a[idx]);
	mpq_mul(aux, aux, v[i].coeff.q);
	mpq_sub(qr, qr, aux);
	break;
      }
    } else {
      idx = untag_idx(idx);
      switch (buffer->tag[idx]) {
      case NO_COEFF:
	break;

      case MPQ_COEFF:
	// qr := qr - buffer->q[idx] * v[i].coeff.a
	mpq_set_from_int(aux, v[i].coeff.a);
	mpq_mul(aux, aux, buffer->q[idx]);
	mpq_sub(qr, qr, aux);
	break;

      case INT_COEFF:
	// ar := ar - buffer->a[idx] * v[i].coeff.a
	// we have buffer->a[idx] <= NORMAL_CONST
	//    and  v[i].coeff.a <= NORMAL_CONST
	prod = buffer->a[idx] * v[i].coeff.a;
	if (abs(ar) >= INT_MAX - abs(prod)) {
	  // overflow is possible: move ar into qr
	  mpq_set_from_int(aux, ar);
	  mpq_add(qr, qr, aux);
	  ar = 0;
	}
	ar -= prod;
	break;
      }
    }    
  }


  // copy (qr + ar) as new coefficient for k
  if (mpq_is_zero(qr) && abs(ar) <= NORMAL_CONST) {
    if (buffer->tag[k] == NO_COEFF) {
      if (ar != 0) {
	buffer->tag[k] = INT_COEFF;
	buffer->a[k] = ar;
	i = buffer->nelems;
	buffer->active[i] = k;
	buffer->nelems = i+1;
      }
    } else {
      buffer->tag[k] = INT_COEFF;
      buffer->a[k] = ar;
    }
  } else {
    // qr is buffer->q[k]
    // qr := qr + ar
    mpq_set_from_int(aux, ar);
    mpq_add(qr, qr, aux);
    if (mpq_is_zero(qr)) {
      if (buffer->tag[k] != NO_COEFF) {
	buffer->a[k] = 0;
	buffer->tag[k] = INT_COEFF;
      }
    } else {
      buffer->tag[k] = MPQ_COEFF;
      if (buffer->tag[k] == NO_COEFF) {
	i = buffer->nelems;
	buffer->active[i] = k;
	buffer->nelems = i + 1;
      }
    }
  }
}


/*
 * Compute buffer := buffer * E^-1
 * where E is an eta-matrix with all coefficients integer
 * - k = column index
 * - v = non-zero elements on column k of E, except diagonal
 * - n = number of elements in v
 */
void product_inv_int_eta(buffer_t *buffer, int k, vector_elem_t *v, int n) {
  int i, idx;
  mpq_ptr qr, aux;
  int ar, prod;

  /*
   * The loop below compute x[k] using qr and ar:
   * at the end of the loop, new coefficient = qr + ar
   */
  qr = buffer->q[k];
  ar = 0;
  switch (buffer->tag[k]) {
  case NO_COEFF:
    mpq_set_from_int(qr, 0);
    break;

  case MPQ_COEFF:
    break;

  case INT_COEFF:
    mpq_set_from_int(qr, 0);
    ar = buffer->a[k];
    break;
  }

  aux = buffer->r0;

  for (i=0; i<n; i++) {
    idx = untag_idx(v[i].idx);
    switch (buffer->tag[idx]) {
    case NO_COEFF:
      break;

    case MPQ_COEFF:
      // qr := qr - buffer->q[idx] * v[i].coeff.a
      mpq_set_from_int(aux, v[i].coeff.a);
      mpq_mul(aux, aux, buffer->q[idx]);
      mpq_sub(qr, qr, aux);
      break;

    case INT_COEFF:
      // ar := ar + buffer->a[idx] * v[i].coeff.a
      // we have buffer->a[idx] <= NORMAL_CONST
      //    and  v[i].coeff.a <= NORMAL_CONST
      prod = buffer->a[idx] * v[i].coeff.a;
      if (abs(ar) >= INT_MAX - abs(prod)) {
	// overflow is possible: move ar into qr
	mpq_set_from_int(aux, ar);
	mpq_add(qr, qr, aux);
	ar = 0;
      }
      ar -= prod;
      break;
    }
  }    

  // copy (qr + ar) as new coefficient for k
  if (mpq_is_zero(qr) && abs(ar) <= NORMAL_CONST) {
    if (buffer->tag[k] == NO_COEFF) {
      if (ar != 0) {
	buffer->tag[k] = INT_COEFF;
	buffer->a[k] = ar;
	i = buffer->nelems;
	buffer->active[i] = k;
	buffer->nelems = i+1;
      }
    } else {
      buffer->tag[k] = INT_COEFF;
      buffer->a[k] = ar;
    }
  } else {
    // qr is buffer->q[k]
    // qr := qr + ar
    mpq_set_from_int(aux, ar);
    mpq_add(qr, qr, aux);
    if (mpq_is_zero(qr)) {
      if (buffer->tag[k] != NO_COEFF) {
	buffer->a[k] = 0;
	buffer->tag[k] = INT_COEFF;
      }
    } else {
      buffer->tag[k] = MPQ_COEFF;
      if (buffer->tag[k] == NO_COEFF) {
	i = buffer->nelems;
	buffer->active[i] = k;
	buffer->nelems = i + 1;
      }
    }
  }
}
