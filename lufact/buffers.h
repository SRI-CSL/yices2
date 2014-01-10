/*
 * Operations on buffers
 */

#ifndef __BUFFERS_H
#define __BUFFERS_H

#include "matrix_types.h"

/*
 * Allocate and initialize a buffer of dimension n, 
 */
extern buffer_t *new_buffer(int n);


/*
 * Set the dimension of buffer to n
 * - no effect if dimension is >= n
 * - otherwise buffer dimension is increased to n
 * The content of buffer is kept unchanged.
 */
extern void resize_buffer(buffer_t *buffer, int n);


/*
 * Delete buffer. No effect if buffer is NULL.
 */
extern void delete_buffer(buffer_t *buffer);


/*
 * Normalize buffer:
 * - remove zero coefficients
 * - normalize the rationals
 */
extern void normalize_buffer(buffer_t *buffer);


/*
 * Empty buffer: set all coeff to 0.
 */
extern void clear_buffer(buffer_t *buffer);



/*
 * Permute content of buffer:
 * - buffer is updated so that new_b[p[i]] := old_b[i]
 *   i.e., index i is mapped to p[i]
 * - aux is modified and must be of size at least
 *   equal to buffer->nelems.
 * - p is the permutation mapping (It must be a permutation;
 *   bad things will happen if p[i] = p[j] and i != j).
 */
extern void permute_buffer(buffer_t *buffer, int *p, rat_t *aux);



/****************************************
 *  Set individual elements in a buffer *
 ***************************************/

extern void set_int_elem_in_buffer(buffer_t *buffer, int idx, int value);

extern void set_mpq_elem_in_buffer(buffer_t *buffer, int idx, mpq_ptr value);

extern void set_si_elem_in_buffer(buffer_t *buffer, int idx, long num, unsigned long den);

extern void set_rat_elem_in_buffer(buffer_t *buffer, int idx, rat_t *value);





/**************************************************************
 * Vector operations: buffer is not automatically resized in  *
 * these operations. Call resize_buffer before if needed.     *
 *************************************************************/

/*
 * Copy array of vector elements into buffer
 * n = number of elements in the array
 * buffer must be empty.
 */
extern void copy_vectelem_in_buffer(buffer_t *buffer, vector_elem_t *v, int n);


/*
 * Copy opposite of v into buffer
 * n = number of elements in the array
 * buffer must be empty
 */
extern void copy_opposite_vectelem_in_buffer(buffer_t *buffer, vector_elem_t *v, int n);


/*
 * Copy vector v in buffer.
 * buffer must be empty.
 */
extern void copy_vector_in_buffer(buffer_t *buffer, vector_t *v);


/*
 * Copy the opposite of vector v in buffer. buffer must be empty
 */
extern void copy_opposite_vector_in_buffer(buffer_t *buffer, vector_t *v);


/*
 * Copy a matrix vector into buffer. buffer must be empty.
 */
extern void copy_mat_vector_in_buffer(buffer_t *buffer, mat_vector_t *v);


/*
 * Copy the opposite of a matrix vector into buffer. buffer must be empty.
 */
extern void copy_opposite_mat_vector_in_buffer(buffer_t *buffer, mat_vector_t *v);




/*
 * Add array of n vector_elements to buffer
 */
extern void add_vectelem_to_buffer(buffer_t *buffer, vector_elem_t *v, int n);


/*
 * Subtract array of n vector elements from buffer
 */
extern void sub_vectelem_from_buffer(buffer_t *buffer, vector_elem_t *v, int n);


/*
 * Add s * v to buffer where v is an array of n vector_elements
 */
extern void addmul_vectelem_to_buffer(buffer_t *buffer, vector_elem_t *v, int n, rat_t *s);


/*
 * Subtract s * v from buffer.
 */
extern void submul_vectelem_from_buffer(buffer_t *buffer, vector_elem_t *v, int n, rat_t *s);


/*
 * Add vector to buffer
 */
extern void add_vector_to_buffer(buffer_t *buffer, vector_t *v);

/*
 * Subtract vector from buffer
 */
extern void sub_vector_from_buffer(buffer_t *buffer, vector_t *v);

/*
 * Add s * vector to buffer for a rational s
 */
extern void addmul_vector_to_buffer(buffer_t *buffer, vector_t *v, rat_t *s);

/*
 * Subtract s * vector from buffer for a rational s
 */
extern void submul_vector_from_buffer(buffer_t *buffer, vector_t *v, rat_t *s);




/*
 * Add matrix vector v to buffer
 */
extern void add_mat_vector_to_buffer(buffer_t *buffer, mat_vector_t *v);

/*
 * Subtract matrix vector from buffer
 */
extern void sub_mat_vector_from_buffer(buffer_t *buffer, mat_vector_t *v);

/*
 * Add s * matrix-vector to buffer for a rational s
 */
extern void addmul_mat_vector_to_buffer(buffer_t *buffer, mat_vector_t *v, rat_t *s);

/*
 * Subtract s * mat_vector from buffer for a rational s
 */
extern void submul_mat_vector_from_buffer(buffer_t *buffer, mat_vector_t *v, rat_t *s);



/*
 * OPERATION WITH ETA VECTOR
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
extern void product_inv_eta(buffer_t *buffer, int k, vector_elem_t *v, int n);



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
void equa_solve_step(buffer_t *buffer, mat_vector_t *v, int d_ptr);

#endif /* __BUFFERS_H */
