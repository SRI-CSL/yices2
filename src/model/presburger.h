/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */



#ifndef __PRESBURGER_H
#define __PRESBURGER_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/terms.h"
#include "terms/term_manager.h"

/*
 * Error codes for presburger_add_constraint
 * - a term is rejected if it's not a presburger literal
 * - or if it's an arithmetic disequality (e.g., (not (= x y)))
 * - or if it's false in the model
 */
enum {
  PRES_ERROR_NOT_PRESBURGER_LITERAL = -1,
  PRES_ERROR_ARITH_DISEQ = -2,
  PRES_ERROR_FALSE_LITERAL = -3,
};


/*
 * Presburger projector data structure:
 * - pointers to the relevant term table and term manager
 */
typedef struct presburger_s {
  term_table_t *terms;
  term_manager_t *manager;

} presburger_t;


extern bool is_presburger_literal(term_table_t *table, term_t t);

/*
 * Initialize projector
 * - mngr = relevant term manager
 * - n = initial size (total number of variables)
 * - m = initial esize (number of variables to eliminate)
 * - n must be no more than m
 *
 */
extern void init_presburger_projector(presburger_t *pres, term_manager_t *mngr, uint32_t n, uint32_t m);


/*
 * Reset:
 * - remove all variables and constraints
 * - reset all internal tables.
 */
extern void reset_presburger_projector(presburger_t *pres);


/*
 * Delete: free memory
 */
extern void delete_presburger_projector(presburger_t *pres);


/*
 * Add variable x
 * - x must be a valid term index in proj->terms
 * - x must be distinct from all previously added variables
 * - if to_elim is true then x is a marked as a variable to 
 *   eliminate, otherwise x is a variable to keep
 * - q = value of x in the model
 * - proj must not have any constraints: all variables must be
 *   declared before the first call to presburger_add_constraint 
 */
extern void presburger_add_var(presburger_t *pres, term_t x, bool to_elim, rational_t *q);


/*
 * Add constraint c
 * - c must be true_term or an arithmetic predicate in 
 *   one of the following forms
 *    (ARITH_EQ_ATOM t)
 *    (ARITH_BINEQ_ATOM t1 t2)
 *    (ARITH_GE_ATOM t)
 *    (NOT (ARITH_GE_ATOM t))
 *    (ARITH_DIVIDES_ATOM k t)
 *    (NOT (ARITH_DIVIDES_ATOM k t))
 *   where t, t1, t2 are either variables declared in proj or linear
 *   polynomials in variables declared in proj
 * - c must be true in the model specified by calls to presburger_add_var
 * - no variables can be added after this function is called
 *
 * Return code:
 * - 0 means that c was accepted and added to the set of constraints
 * - a negative code means that c is rejected:
 *   - PRES_ERROR_NOT_PRESBURGER_LITERAL means that c is not a presburger literal
 *   - PRES_ERROR_ARITH_DISEQ means that c is either (NOT (ARITH_EQ_ATOM t))
 *                 or (NOT (ARITH_BINEQ_ATOM t1 t2))
 *   - PRES_ERROR_FALSE_ATOM means that c is 'false_term'.
 *
 * Notes:
 * - the error checks are not exhaustive: we don't check whether c
 *   is true in the model.
 * - the literals (distinct t1 ... tn) and (not (distinct t1 ... tn))
 *   are rejected with error code NOT_ARITH_LITERAL, even if t1 ... t_n
 *   are arithmetic terms.
 */
extern int32_t presburger_add_constraint(presburger_t *pres, term_t c);


/*
 * Apply the variable elimination procedure
 * - no variable or constraint can be added after this function is called.
 */
extern void presburger_eliminate(presburger_t *pres);



/*
 * Collect the result as a vector of formulas
 * - every constraint in proj->constraint is converted to a Boolean
 *   term that's added to vector v
 * - v is not reset
 *
 * So the set of constraints after in proj->constraint is equivalent to 
 * the conjunction of formulas added to v.
 */
extern void presburger_get_formula_vector(presburger_t *pres, ivector_t *v);


/*
 * Collect the result as a formula:
 * - returns either true_term or a conjunction of arithmetic constraints
 *   that do not contain the eliminated variables.
 */
extern term_t presburger_get_formula(presburger_t *pres);




#endif /* __PRESBURGER_H */
