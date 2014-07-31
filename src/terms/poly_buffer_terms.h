/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
