/*
 * Extensions of yices.h
 * Implemented in yices_api.c
 */

#ifndef __YICES_EXTENSIONS_H
#define __YICES_EXTENSIONS_H

#include "terms.h"
#include "bvlogic_buffers.h"
#include "context.h"

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
 * - otherwise, create term t from b and return the atom (t >= 0)
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


/*
 * Convert a bitvector constant to a term
 * - n = bitsize (must be more than 64 and at most YICES_MAX_BVSIZE)
 * - v = value as an array of k words (k = ceil(n/32)).
 */
extern term_t yices_bvconst_term(uint32_t n, uint32_t *v);


/*
 * Convert a 64bit constant to a term
 * - n = bitsize (must be positive and no more than 64)
 * - c = constant value (must be normalized modulo 2^n)
 */
extern term_t yices_bvconst64_term(uint32_t n, uint64_t c);


/*
 * Convert rational q to a term
 */
extern term_t yices_rational_term(rational_t *q);



/*
 * SUPPORT FOR TYPE-CHECKING
 */

/*
 * Check whether t is a valid arithmetic term
 * - if not set the internal error report:
 *
 * If t is not a valid term:
 *   code = INVALID_TERM 
 *   term1 = t
 *   index = -1
 * If t is not an arithmetic term; 
 *   code = ARITHTERM_REQUIRED
 *   term1 = t
 */
extern bool yices_check_arith_term(term_t t);


/*
 * Check for degree overflow in the product (b * t) 
 * - b must be a buffer obtained via yices_new_arith_buffer().
 * - t must be a valid arithmetic term.
 *
 * Return true if there's no overflow.
 *
 * Return false otherwise and set the error report:
 *   code = DEGREE_OVERFLOW
 *   badval = degree of b + degree of t
 */
extern bool yices_check_mul_term(arith_buffer_t *b, term_t t);


/*
 * Same thing for the product of two buffers b1 and b2.
 * - both must be buffers allocated using yices_new_arith_buffer().
 */
extern bool yices_check_mul_buffer(arith_buffer_t *b1, arith_buffer_t *b2);



/*
 * Check whether n <= YICES_MAX_BVSIZE and if not set the error report:
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = n
 */
extern bool yices_check_bvsize(uint32_t n);


/*
 * Check whether t is a valid bit-vector term
 * - if not set the internal error report.
 *
 * If t is not a valid term:
 *   code = INVALID_TERM 
 *   term1 = t
 *   index = -1
 * If t is not an arithmetic term; 
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 */
extern bool yices_check_bv_term(term_t t);


/*
 * Check whether buffer b is non-empty (i.e., can be converted to a term).
 * - return false if b is empty and set the error report (code = EMPTY_BITVECTOR).
 * - return true if b is non-empty.
 */
extern bool yices_check_bvlogic_buffer(bvlogic_buffer_t *b);


/*
 * Checks for degree overflow in bitvector multiplication:
 * - four variants depending on the type of buffer used
 *   and on whether the argument is a term or a buffer
 *
 * In all cases, the function set the error report and
 * return false if there's an overflow:
 *   code = DEGREE_OVEFLOW
 *   badval = degree of the product
 *
 * All return true if there's no overflow.
 */
extern bool yices_check_bvmul64_term(bvarith64_buffer_t *b, term_t t);
extern bool yices_check_bvmul64_buffer(bvarith64_buffer_t *b1, bvarith64_buffer_t *b2);

extern bool yices_check_bvmul_term(bvarith_buffer_t *b, term_t t);
extern bool yices_check_bvmul_buffer(bvarith_buffer_t *b1, bvarith_buffer_t *b2);


/*
 * Check whether s is a valid shift amount for buffer b:
 * - return true if 0 <= s <= b->bitsize
 * - otherwise set the error report and return false.
 */
extern bool yices_check_bitshift(bvlogic_buffer_t *b, int32_t s);


/*
 * Check whether [i, j] is a valid segment for a bitvector of size n
 * - return true if 0 <= i <= j < n
 * - otherwise set the error report and return false.
 */
extern bool yices_check_bvextract(uint32_t n, int32_t i, int32_t j);


/*
 * Check whether repeat_concat(b, n) is valid
 * - return true if 0 <= n and (n * b->bitsize) <= MAX_BVSIZE
 * - return false and set error report otherwise.
 */
extern bool yices_check_bvrepeat(bvlogic_buffer_t *b, int32_t n);


/*
 * Check whether sign_extend(b, n) or zero_extend(b, n) is valid
 * - return true if 0 <= m, b->bitsize != 0 and n + b->bitsize <= MAX_BVSIZE
 * - return false and set error report otherwise.
 */
extern bool yices_check_bvextend(bvlogic_buffer_t *b, int32_t n);


/*
 * CONTEXT INITILIZATION
 */

/*
 * Return a new context for the given arch, mode, iflag, and qflag.
 * This doesn't use the configuration object, unlike the official 
 * yices_new_context declared in yices.h.
 * - arch = architecture to use
 * - mode = which optional features are supported
 * - iflag = true to active the integer solver
 * - qflag = true to support quantifiers
 *
 * The following simplification options are enabled:
 * - variable elimination
 * - eq_abstraction
 * - diseq/or flattening
 * - arithvar and bvarithvar elimination
 */
extern context_t *yices_create_context(context_arch_t arch, context_mode_t mode,
                                       bool iflag, bool qflag);


/*
 * Set default search parameters for ctx (based on architecture and theories) 
 * - this is based on benchmarking on the SMT-LIB 1.2 benchmarks (cf. yices_smtcomp.c)
 */
extern void yices_set_default_params(context_t *ctx, param_t *params);


#endif /* __YICES_EXTENSIONS_H */
