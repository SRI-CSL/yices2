/*
 * OPERATION COMBINING BIT-VECTOR BUFFERS AND TERMS
 */

#ifndef __BVLOGIC_BUFFER_TERMS_H
#define __BVLOGIC_BUFFER_TERMS_H

#include "bvlogic_buffers.h"
#include "terms.h"


/*
 * Assignment and binary operations:
 * - all operations update buffer b
 * - term t must be a bitvector term defined in the term table
 * - for all binary operations, t must have the same bitsize as b
 */
extern void bvlogic_buffer_set_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);

extern void bvlogic_buffer_and_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);
extern void bvlogic_buffer_or_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);
extern void bvlogic_buffer_xor_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);
extern void bvlogic_buffer_concat_left_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);
extern void bvlogic_buffer_concat_right_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);
extern void bvlogic_buffer_comp_bitarray(bvlogic_buffer_t *b, term_table_t *table, term_t t);


/*
 * Convert b to a term
 */
extern term_t bvlogic_buffer_get_term(bvlogic_buffer_t *b, term_table_t *table);



#endif /* __BVLOGIC_BUFFER_TERMS_H */
