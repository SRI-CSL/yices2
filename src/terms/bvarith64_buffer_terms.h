/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BIT-VECTOR ARITHMETIC OPERATIONS THAT MIX BUFFERS AND TERMS
 */

#ifndef __BVARITH64_BUFFER_TERMS_H
#define __BVARITH64_BUFFER_TERMS_H

#include "terms/bvarith64_buffers.h"
#include "terms/terms.h"


/*
 * Copy t's value into buffer b
 * - t must be defined in table and be a bitvector term
 * - b->ptbl must be the same as table->pprods
 */
extern void bvarith64_buffer_set_term(bvarith64_buffer_t *b, term_table_t *table, term_t t);


/*
 * Operations on buffer b:
 * - t must be defined in table and be a bitvector term
 *   of same bitsize as buffer b
 * - b->ptbl must be the same as table-pprods
 */
extern void bvarith64_buffer_add_term(bvarith64_buffer_t *b, term_table_t *table, term_t t);
extern void bvarith64_buffer_sub_term(bvarith64_buffer_t *b, term_table_t *table, term_t t);
extern void bvarith64_buffer_mul_term(bvarith64_buffer_t *b, term_table_t *table, term_t t);


/*
 * Add a * t to b
 * - t must be defined in table and be a bitvector term of same bitsize as b
 * - b->ptbl must be the same as table->pprods
 */
extern void bvarith64_buffer_add_const_times_term(bvarith64_buffer_t *b, term_table_t *table, uint64_t a, term_t t);


/*
 * Multiply b by (t ^ d)
 * - t must be defined in table and be a bitvector term of same bitsize as b
 * - b->ptbl must be the same as table->pprods
 */
extern void bvarith64_buffer_mul_term_power(bvarith64_buffer_t *b, term_table_t *table, term_t t, uint32_t d);


#endif /*  __BVARITH64_BUFFER_TERMS_H */
