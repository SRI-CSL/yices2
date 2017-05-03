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
 * ARITHMETIC OPERATIONS INVOLVING BALANCED BUFFERS AND TERMS
 */

#ifndef __RBA_BUFFER_TERMS_H
#define __RBA_BUFFER_TERMS_H

#include "terms/balanced_arith_buffers.h"
#include "terms/terms.h"


/*
 * Binary operations:
 * - t must be defined in table and must be an arithmetic term
 *   (i.e., t must have type int or real)
 * - b->ptbl must be the same as table->pprods
 *
 * All operations update the buffer.
 */
extern void rba_buffer_add_term(rba_buffer_t *b, term_table_t *table, term_t t);
extern void rba_buffer_sub_term(rba_buffer_t *b, term_table_t *table, term_t t);
extern void rba_buffer_mul_term(rba_buffer_t *b, term_table_t *table, term_t t);

extern void rba_buffer_add_const_times_term(rba_buffer_t *b, term_table_t *table, rational_t *a, term_t t);

extern void rba_buffer_mul_term_power(rba_buffer_t *b, term_table_t *table, term_t t, uint32_t d);



#endif /* __RBA_BUFFER_TERMS_H */
