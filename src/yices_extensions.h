/*
 * Extensions of yices.h
 * Implemented in term_api.c
 */

#ifndef __YICES_EXTENSIONS_H
#define __YICES_EXTENSIONS_H

#include "yices_types.h"

/***************************************
 * EXTENSIONS FOR BITVECTOR CONSTANTS  *
 **************************************/

/*
 * These functions are similar to the bvarith_xxx_const and bvlogic_xxx_const 
 * but the  bitvector constant is represented directly as a byte array.
 * For all operations, 
 * - n = bitsize of the constant,
 * - bv = byte array storing the constant. bv must be normalized.
 *
 * Error codes are set as in the other bitvector functions.  Only the
 * functions that may generate error codes are implemented here.  For
 * other functions, direct call of the bvarith_expr and bvlogic_expr
 * functions can be used.
 */
extern int32_t yices_bvarith_add_bvconst(bvarith_buffer_t *b, uint32_t n, uint32_t *bv);
extern int32_t yices_bvarith_sub_bvconst(bvarith_buffer_t *b, uint32_t n, uint32_t *bv);
extern int32_t yices_bvarith_mul_bvconst(bvarith_buffer_t *b, uint32_t n, uint32_t *bv);

extern int32_t yices_bvlogic_and_bvconst(bvlogic_buffer_t *b, uint32_t n, uint32_t *bv);
extern int32_t yices_bvlogic_or_bvconst(bvlogic_buffer_t *b, uint32_t n, uint32_t *bv);
extern int32_t yices_bvlogic_xor_bvconst(bvlogic_buffer_t *b, uint32_t n, uint32_t *bv);
extern int32_t yices_bvlogic_nand_bvconst(bvlogic_buffer_t *b, uint32_t n, uint32_t *bv);
extern int32_t yices_bvlogic_nor_bvconst(bvlogic_buffer_t *b, uint32_t n, uint32_t *bv);
extern int32_t yices_bvlogic_xnor_bvconst(bvlogic_buffer_t *b, uint32_t n, uint32_t *bv);

extern int32_t yices_bvlogic_comp_bvconst(bvlogic_buffer_t *b, uint32_t n, uint32_t *bv);


/*
 * Shift by k bits, where k is a bitvector constant.  For large k,
 * this does not cause an error but it sets the result 0bxxxxx where x
 * is either 0 or 1.
 * - returns -1 if n != b->nbits, 0 otherwise
 * 
 * Error report:
 *   code = INCOMPATIBLE_BVSIZES
 *   badval = n 
 */
extern int32_t yices_bvlogic_shl_bvconst(bvlogic_buffer_t *b, uint32_t n, uint32_t *bv);
extern int32_t yices_bvlogic_lshr_bvconst(bvlogic_buffer_t *b, uint32_t n, uint32_t *bv);
extern int32_t yices_bvlogic_ashr_bvconst(bvlogic_buffer_t *b, uint32_t n, uint32_t *bv);


/*
 * Direct construction of a bvconst term. Fail if n is zero.
 */
extern term_t yices_bvconst_term(uint32_t n, uint32_t *bv);


/*
 * Generic constructor for bitvector operations
 */
extern term_t yices_bvoperator(uint32_t op, term_t t1, term_t t2);


#endif /* __YICES_EXTENSIONS_H */
