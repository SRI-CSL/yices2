/*
 * Extensions of yices.h
 * Implemented in term_api.c
 */

#ifndef __YICES_EXTENSIONS_H
#define __YICES_EXTENSIONS_H

#include "terms.h"
#include "bvlogic_buffers.h"


/*
 * BUFFER ALLOCATION/FREE
 */

/*
 * All buffer allocation functions can be used only after yices_init() has been called.
 */

/*
 * Allocate an arithmetic buffer, initialized to the zero polynomial.
 */
extern arith_buffer_t *yices_new_arith_buffer(void);

/*
 * Free a buffer returned by the previous function.
 */
extern void yices_free_arith_buffer(arith_buffer_t *b);

/*
 * Allocate and initialize a bvarith_buffer
 * - the buffer is initialized to 0b0...0 (with n bits)
 * - n must be positive and no more than YICES_MAX_BVSIZE
 */
extern bvarith_buffer_t *yices_new_bvarith_buffer(uint32_t n);

/*
 * Free an allocated bvarith_buffer
 */
extern void yices_free_bvarith_buffer(bvarith_buffer_t *b);

/*
 * Allocate and initialize a bvarith64_buffer
 * - the buffer is initialized to 0b0000..0 (with n bits)
 * - n must be between 1 and 64
 */
extern bvarith64_buffer_t *yices_new_bvarith64_buffer(uint32_t n);

/*
 * Free an allocated bvarith64_buffer
 */
extern void yices_free_bvarith64_buffer(bvarith64_buffer_t *b);

/*
 * Allocate and initialize a bvlogic buffer
 * - the buffer is empty (bitsize = 0)
 */
extern bvlogic_buffer_t *yices_new_bvlogic_buffer(void);

/*
 * Free buffer b allocated by the previous function
 */
extern void yices_free_bvlogic_buffer(bvlogic_buffer_t *b);



/*
 * CONVERSION TO TERMS
 */

/*
 * Convert b to a term and reset b.
 *
 * Normalize b first then apply the following simplification rules:
 * 1) if b is a constant, then a constant rational is created
 * 2) if b is of the form 1.t then t is returned
 * 3) if b is of the form 1.t_1^d_1 x ... x t_n^d_n, then a power product is returned
 * 4) otherwise, a polynomial term is returned
 */
extern term_t arith_buffer_get_term(arith_buffer_t *b);

/*
 * Construct the atom (b == 0) then reset b.
 *
 * Normalize b first.
 * - simplify to true if b is the zero polynomial
 * - simplify to false if b is constant and non-zero
 * - rewrite to (t1 == t2) if that's possible.
 * - otherwise, create a polynomial term t from b
 *   and return the atom (t == 0).
 */
extern term_t arith_buffer_get_eq0_atom(arith_buffer_t *b);

/*
 * Construct the atom (b >= 0) then reset b.
 *
 * Normalize b first then check for simplifications.
 * - simplify to true or false if b is a constant
 * - otherwise term t from b and return the atom (t >= 0)
 */
extern term_t arith_buffer_get_geq0_atom(arith_buffer_t *b);

/*
 * Atom (b <= 0): rewritten to (-b >= 0)
 */
extern term_t arith_buffer_get_leq0_atom(arith_buffer_t *b);

/*
 * Atom (b > 0): rewritten to (not (b <= 0))
 */
extern term_t arith_buffer_get_gt0_atom(arith_buffer_t *b);

/*
 * Atom (b < 0): rewritten to (not (b >= 0))
 */
extern term_t arith_buffer_get_lt0_atom(arith_buffer_t *b);


/*
 * Convert b to a term then reset b.
 * - b must not be empty.
 * - build a bitvector constant if possible
 * - if b is of the form (select 0 t) ... (select k t) and t has bitsize (k+1)
 *   then return t
 * - otherwise build a bitarray term
 */
extern term_t bvlogic_buffer_get_term(bvlogic_buffer_t *b);

/*
 * Normalize b then convert it to a term and reset b
 *
 * if b is reduced to a single variable x, return the term attached to x
 * if b is reduced to a power product, return that
 * if b is constant, build a BV_CONSTANT term
 * if b can be converted to a BV_ARRAY term do it
 * otherwise construct a BV_POLY
 */
extern term_t bvarith_buffer_get_term(bvarith_buffer_t *b);


/*
 * Normalize b then convert it to a term and reset b
 *
 * if b is reduced to a single variable x, return the term attached to x
 * if b is reduced to a power product, return that
 * if b is constant, build a BV64_CONSTANT term
 * if b can be converted to a BV_ARRAY term do it
 * otherwise construct a BV64_POLY
 */
extern term_t bvarith64_buffer_get_term(bvarith64_buffer_t *b);

#endif /* __YICES_EXTENSIONS_H */
