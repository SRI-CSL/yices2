/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
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
