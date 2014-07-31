/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BIT-VECTOR ARITHMETIC OPERATIONS THAT MIX BUFFERS AND TERMS
 */

#ifndef __BVARITH_BUFFER_TERMS_H
#define __BVARITH_BUFFER_TERMS_H

#include "terms/bvarith_buffers.h"
#include "terms/terms.h"


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
 * - b->ptbl must be the same as table->pprods
 */
extern void bvarith_buffer_add_term(bvarith_buffer_t *b, term_table_t *table, term_t t);
extern void bvarith_buffer_sub_term(bvarith_buffer_t *b, term_table_t *table, term_t t);
extern void bvarith_buffer_mul_term(bvarith_buffer_t *b, term_table_t *table, term_t t);


/*
 * Add a * t to b
 * - t must be defined in table and be a bitvector term of same bitsize as b
 * - a must be have the same bitsize as b (as many words a b->width)
 * - b->ptbl must be the same as table->pprods
 */
extern void bvarith_buffer_add_const_times_term(bvarith_buffer_t *b, term_table_t *table, uint32_t *a, term_t t);


/*
 * Multiply b by (t ^ d)
 * - t must be defined in table and be a bitvector term of same bitsize as b
 * - b->ptbl must be the same as table->pprods
 */
extern void bvarith_buffer_mul_term_power(bvarith_buffer_t *b, term_table_t *table, term_t t, uint32_t d);



#endif /*  __BVARITH_BUFFER_TERMS_H */
