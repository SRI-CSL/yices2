/*
 * BETA REDUCTION OF TERMS
 *
 * For now, we implement beta-reduction only at the top-level of a term:
 * - t is reducible if it's of the form (apply (lambda (x_1 ... x_n) u) t_1 ... t_n)
 * - then beta_reduce(t) is u[x_1/t_1 ... x_n/t_n].
 * We don't recursively reduce t's subterms.
 */

#ifndef __BETA_REDUCTION_H
#define __BETA_REDUCTION_H

#include <stdbool.h>

#include "term_manager.h"


/*
 * Check whether t is reducible
 */
extern bool beta_reducible(term_table_t *table, term_t t);


/*
 * Apply reduction to t
 * - if t is not of the from (apply (lambda (x_1 ... x_n) u) t_1 ... t_n) then 
 *   it's returned unchanged
 * - otherwise, apply the substitution [x_1 := t_1, ... x_n := t_n] to u and return
 *   the result
 *
 * Possible error codes are the same as in apply_term_subst:
 * - return -1 (NULL_TERM) if the substitution causes a degree overflow
 * - return -2 if an exception is raised (bug somewhere)
 */
extern term_t beta_reduce(term_manager_t *mngr, term_t t);


#endif /* __BETA_REDUCTION_H */
