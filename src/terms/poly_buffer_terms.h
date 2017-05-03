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
 * ARITHMETIC OPERATIONS INVOLVING POLY_BUFFERS AND TERMS
 */

#ifndef __POLY_BUFFER_TERMS_H
#define __POLY_BUFFER_TERMS_H

#include "terms/poly_buffer.h"
#include "terms/terms.h"


/*
 * Add/subtract a * t to/from buffer b
 * - b is not normalized
 */
extern void poly_buffer_addmul_term(term_table_t *terms, poly_buffer_t *b, term_t t, rational_t *a);
extern void poly_buffer_submul_term(term_table_t *terms, poly_buffer_t *b, term_t t, rational_t *a);

extern void poly_buffer_add_term(term_table_t *terms, poly_buffer_t *b, term_t t);
extern void poly_buffer_sub_term(term_table_t *terms, poly_buffer_t *b, term_t t);


#endif /* __POLY_BUFFER_TERMS_H */
