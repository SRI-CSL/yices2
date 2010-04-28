/*
 * MISCELANEOUS COMPUTATIONS ON TERMS
 */

/*
 * terms.h and terms.c implement basic term construction
 * functions.
 *
 * We put here helper functions to support rewriting and simplification,
 */

#ifndef __TERM_UTILS_H
#define __TERM_UTILS_H

#include <stdbool.h>

#include "bv_constants.h"
#include "terms.h"


/*
 * Check whether two terms x and y can never be equal.
 * This is incomplete and can detect disequalities in simple cases.
 * - if the function returns true, then x and y can't be equal in any interpretation 
 * - if if returns false, we don't know.
 */
extern bool disequal_terms(term_table_t *tbl, term_t x, term_t y);


/*
 * Check whether a[i] can't equal b[i] for all i in 0 .. n-1
 */
extern bool disequal_term_arrays(term_table_t *tbl, uint32_t n, term_t *a, term_t *b);


/*
 * Check whether all the elements of a are disequal
 * this can be expensive: quadratic cost, 
 * but should fail quickly on most examples
 */
extern bool pairwise_disequal_terms(term_table_t *tbl, uint32_t n, term_t *a);


/*
 * Compute an uppper/lower bound on a bitvector term t 
 * - the result is stored in c
 * - there are two cases, depending on whether t is interpreted
 *   as a signed (2's complement) or as an unsigned number.
 */
extern void upper_bound_unsigned(term_table_t *tbl, term_t t, bvconstant_t *c);
extern void lower_bound_unsigned(term_table_t *tbl, term_t t, bvconstant_t *c);
extern void upper_bound_signed(term_table_t *tbl, term_t t, bvconstant_t *c);
extern void lower_bound_sigend(term_table_t *tbl, term_t t, bvconstant_t *c);


/*
 * Same thing for a bitvector term of 1 to 64 bits
 * - return the bound as an unsigned 64-bit integer
 *   (padded with 0s if the bitsize is less than 64)
 * This is true even for signed bounds, the result is never
 * sign extended to 64 bits.
 */
extern uint64_t upper_bound_unsigned64(term_table_t *tbl, term_t t);
extern uint64_t lower_bound_unsigned64(term_table_t *tbl, term_t t);
extern uint64_t upper_bound_signed64(term_table_t *tbl, term_t t);
extern uint64_t lower_bound_signed64(term_table_t *tbl, term_t t);



#endif /* __TERM_UTILS_H */
