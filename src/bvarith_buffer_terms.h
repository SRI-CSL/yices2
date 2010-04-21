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



#endif /*  __BVARITH_BUFFER_TERMS_H */
