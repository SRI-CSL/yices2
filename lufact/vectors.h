/*
 * Operations on sparse vectors
 */

#ifndef __VECTORS_H
#define __VECTORS_H

#include <gmp.h>
#include "matrix_types.h"

/**
 * Create a new vector of initial capacity n
 * - n must be non-negative
 * - the vector is initially empty
 */
extern vector_t *new_vector(int n);


/**
 * Make *v large enough for at least n elements
 * - change the capacity, keep all elements already in v
 * - if *v is NULL, allocate a vector of capacity n
 */
extern void adjust_vector_capacity(vector_t **v, int n);

/**
 * Shrink *v so that its capacity equals its size
 */
extern void shrink_vector(vector_t **v);

/**
 * Release all mpq elements of v then delete v
 */
extern void cleanup_and_delete_vector(vector_t *v);

/**
 * Less safe version: just delete v.
 * To prevent memory leaks, the mpq elements of v must be 
 * freed.
 */
extern void delete_vector(vector_t *v);


/**
 * Release all rationals elements of v then empty v
 */
extern void empty_vector(vector_t *v);


/**
 * Add element <i, a> at the end of vector *v
 * - resize *v if it's full
 * - allocate a new vector of default size if *v is NULL
 */
extern void add_int_elem_to_vector(vector_t **v, int i, int a);


/**
 * Add element <i, q> at the end of vector *v
 * - resize *v if it's full
 * - allocate a new vector of default size if *v is NULL
 */
extern void add_mpq_elem_to_vector(vector_t **v, int i, mpq_ptr q);


/**
 * Add element <i, num/den> at the end of *v.
 */
extern void add_si_elem_to_vector(vector_t **v, int i, long num, unsigned long den);


/**
 * Add element <i, r> at the end of *v
 */
extern void add_rat_elem_to_vector(vector_t **v, int i, rat_t *r);



/**
 * Unsafe versions of the add operations: do not check for size.
 * - must be called with v initialized and not full:
 *    (v != NULL) and v->size < v->capacity.
 */
extern void fast_add_int_elem_to_vector(vector_t *v, int i, int a);

extern void fast_add_mpq_elem_to_vector(vector_t *v, int i, mpq_ptr q);

extern void fast_add_si_elem_to_vector(vector_t *v, int i, long num, unsigned long den);

extern void fast_add_rat_elem_to_vector(vector_t *v, int i, rat_t *r);


/*
 * Store buffer in vector. Assumes buffer is normalized.
 */
extern void copy_buffer_in_vector(vector_t **v, buffer_t *buffer);


/*
 * Unsafe version: v must be large enough
 */
extern void fast_copy_buffer_in_vector(vector_t *v, buffer_t *buffer);


#endif /* __VECTORS_H */
