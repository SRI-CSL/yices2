/*
 * ARITHMETIC OPERATIONS INVOLVING BUFFERS AND TERMS
 */

#ifndef __ARITH_BUFFER_TERMS_H
#define __ARITH_BUFFER_TERMS_H

#include "arith_buffers.h"
#include "terms.h"


/*
 * Binary oprations:
 * - t must be defined in table and must be an arithmetic term
 *   (i.e., t must have type int or real)
 * - b->ptbl must be the same as table->pprods
 *
 * All operations update the buffer.
 */
extern void arith_buffer_add_term(arith_buffer_t *b, term_table_t *table, term_t t);
extern void arith_buffer_sub_term(arith_buffer_t *b, term_table_t *table, term_t t);
extern void arith_buffer_mul_term(arith_buffer_t *b, term_table_t *table, term_t t);
extern void arith_buffer_add_const_times_term(arith_buffer_t *b, term_table_t *table, 
					      rational_t *a, term_t t);



#if 0


/*
 * Convert b to a term and reset b.
 *
 * The buffer b is normalized first then the following simplification
 * rules are applied:
 * 1) if b is a constant, then a constant rational is created
 * 2) if b is of the form 1.t then t is returned
 * 3) if b is of the form 1.t_1^d_1 x ... x t_n^d_n, then a power product is returned
 * 4) otherwise, a polynomial term is returned
 */
extern term_t arith_buffer_get_term(arith_buffer_t *b, term_table_t *table);


/*
 * Construct the atom (b == 0) then reset b.
 *
 * Normalize b first.
 * simplify to true if b is the zero polynomial
 * simplify to false if b is constant and non-zero
 * rewrite to (t1 == t2) if that's possible.
 */
extern term_t arith_buffer_get_eq0_atom(arith_buffer_t *b, term_table_t *table);


/*
 * Construct the atom (b >= 0) then reset b.
 *
 * Normalize b first then check for simplifications.
 * - simplify to true or false if b is a constant
 * - otherwise term t from b and return the atom (t >= 0)
 */
extern term_t arith_buffer_get_geq0_atom(arith_buffer_t *b, term_table_t *table);


/*
 * More atoms:
 *  (b <= 0) is rewritten to (-b >= 0)
 *  (b > 0)  is rewritten to (not (-b >= 0))
 *  (b < 0)  is rewritten to (not (b >= 0))
 */
extern term_t arith_buffer_get_leq0_atom(arith_buffer_t *b, term_table_t *table);
extern term_t arith_buffer_get_gt0_atom(arith_buffer_t *b, term_table_t *table);
extern term_t arith_buffer_get_lt0_atom(arith_buffer_t *b, term_table_t *table);


#endif

#endif /* __ARITH_BUFFER_TERMS_H */
