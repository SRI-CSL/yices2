/*
 * BIT-VECTOR ARITHMETIC OPERATIONS THAT MIX BUFFERS AND TERMS
 */

#ifndef __BVARITH_BUFFER_TERMS_H 
#define __BVARITH_BUFFER_TERMS_H

#include "bvarith_buffers.h"
#include "terms.h"


/*
 * Copy t's value into buffer b
 * - t must be defined in table and be a bitvector term
 * - b->ptbl must be the same as table->pprods
 */
extern void bvarith_buffer_set_term(bvarith_buffer_t *b, term_table_t *table, term_t t);


/*
 * Operations on buffer b:
 * - t must be defined in table and be a bitvector term
 *   of same bitsize as buffer b
 * - b->ptbl must be the same as table-pprods
 */
extern void bvarith_buffer_add_term(bvarith_buffer_t *b, term_table_t *table, term_t t);
extern void bvarith_buffer_sub_term(bvarith_buffer_t *b, term_table_t *table, term_t t);
extern void bvarith_buffer_mul_term(bvarith_buffer_t *b, term_table_t *table, term_t t);



/*
 * Normalize b then convert it to a term and reset b
 *
 * if b is reduced to a single variable x, return the term x
 * if b is reduced to a power product, return that
 * if b is constant, build a BV_CONSTANT term
 * otherwise construct a BV_POLY
 */
extern term_t bvarith_buffer_get_term(bvarith_buffer_t *b, term_table_t *table);


#endif /*  __BVARITH_BUFFER_TERMS_H */
