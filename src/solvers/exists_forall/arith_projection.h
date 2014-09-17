/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * MODEL-BASED QUANTIFIER ELIMINATION FOR LINEAR ARITHMETIC
 *
 * Given a conjunction A of linear-arithmetic atoms in variables X and Y,
 * and a model M = (X_0, Y_0) of A, we want to construct a formula E(X) 
 * such that
 *
 *   1) E(X) under approximates (EXISTS Y: A(X, Y))
 *      we want E(X) => EXISTS Y: A(X, Y)
 *
 *   2) E(X_0) is true.
 *
 *
 * Assumptions
 * -----------
 * - all atoms in A are linear equalities or (strict) inequalities in X and Y
 *   (i.e., nothing of the form  P /= 0)
 * - we can then represent A as a set of constraint of the form
 *        a_1 x_1 + ... + b_1 y_1 + ... + c = 0
 *     or a_1 x_1 + ... + b_1 y_1 + ... + c >= 0
 *     or a_1 x_1 + ... + b_1 y_1 + ... + c > 0
 *
 * Algorithms
 * ----------
 * 1) Gaussian elimination: If b_k /= 0, we rewrite 
 *      a_1 x_1 + .. + b_k y_k + ... + c  =0
 *    to y_k = <linear expression> and subsitute y_k with
 *    the expression everywhere.
 *
 * 2) Fourier-Motzkin: The basic Fourier-Motzkin step takes
 *    two inequalities where y occurs with opposite signs then 
 *    adds an implied inequality that doesn't contain y.
 *
 *    Example: from 
 *       p_1 + a_1 y >= 0 with a_1 > 0 
 *       p_2 + a_2 y > 0 with a_2 < 0
 *   we get:
 *       p_1/a_1 + y >= 0
 *      -p_2/a_2 - y > 0
 *   which implies
 *        p1/a_1 - p2/a2 > 0.
 *
 *   This can quickly blow up so we limit Fourier-Motzkin to cheap cases.
 *   We count the number of inequalities where y occurs with a positive
 *   coefficients and the number of inequalities where y has a negative
 *   coefficients. Then Fourier-Mozkin is cheap if either counter is 0,
 *   or one of them is 1, or both of them are 2.
 *
 * 3) Virtual Term Substitution.  For the remaining variables, we use
 *    the model and virtual term substitution. To eliminate
 *    variable y, we rewrite inequalities involving y into two sets: 
 *    - lower bounds: p_1 <= y, ..., p_k <= y 
 *    - upper bounds: y <= q_1, ..., y <= q_l
 *    We evaluate p_1 .... p_k in the model M and keep the p_i that has
 *    largest value. We do the same thing for q_1 ... q_l and keep the q_j
 *    that has the smallest value. Then we eliminate y by substution:
 *    we replace y by (p_i + q_j)/2 everywhere.
 *
 *
 * Data Structures
 * ---------------
 * A projector object stores the set of constraints + the variables to eliminate
 * and the variables to keep. The model is defined by giving a rational value to
 * all the variables. The intended use is as follows:
 * 
 * 1) initialize a projector object with the right term manager
 * 2) add all the variables one by one and specify their value in the model
 * 3) add the constraints
 * 4) invoke the variable elimination procedure
 * 5) extract the result as a formula or array of formulas (built using the
 *    term manager)
 */

#ifndef __ARITH_PROJECTION_H
#define __ARITH_PROJECTION_H

#include <stdint.h>
#include <stdbool.h>

#include "utils/ptr_sets.h"
#include "terms/terms.h"
#include "terms/term_manager.h"
#include "terms/poly_buffer.h"


/*
 * Tags for identifying the constraint types
 *   APROJ_LT = 00  strict inequality (less than)
 *   APROJ_LE = 01  non-strict inequality
 *   APROJ_EQ = 10  equality
 *
 * Using this encoding, we can compute the resulting tag
 * in a Fourier-Motzking step using bitwise and.
 */
typedef enum {
  APROJ_LT = 0,
  APROJ_LE = 1,
  APROJ_EQ = 2,
} aproj_tag_t;


/*
 * Arithmetic constraint:
 * - tag = constraint type
 * - nterms = number of monomials
 * - mono = array of nterms + 1 monomials
 * we use the same conventions as in polynomials.h:
 * - the monomials are ordered by increasing variable index
 * - mono[nterms] contains the end marker max_idx
 * - const_idx = 0 denotes the constant
 */
typedef struct aproj_constraint_s {
  aproj_tag_t tag;
  uint32_t nterms;
  monomial_t mono;
} aproj_constraint_t;

#define MAX_APROJ_CONSTRAINT_SIZE (((UINT32_MAX-sizeof(aproj_constraint_t))/sizeof(monomial_t)) - 1)


/*
 * Score for a variable to eliminate:
 * - for a variable y, we count
 * - the number of equalities that contain y
 *   the number of inequalities where y occurs with a positive coefficient
 *   the number of inequalities where y occurs with a negative coefficient
 */
typedef struct aproj_score_s {
  uint32_t eq_count;
  uint32_t pos_count;
  uint32_t neg_count;
} aproj_score_t;


/*
 * Variable table
 * - internally, variables are indexed from 1 to nvars
 *   variables to eliminate are indexed from 1 to nelems <= nvars
 * - for each variable, we keep track of
 *   the term it represents (term index in a term table)
 *   its value in the model
 * - for the variables to eliminate, we also keep
 *   the set of constraints in which they occur
 *   and a score = triple of counters
 * - tmap: maps external term index to internal variable index
 *   (so if term_of[x] = t then tmap[t] = x).
 */
typedef struct aproj_vtbl_s {
  uint32_t nvars;   // number of variables
  uint32_t nelims;  // variables to eliminate
  uint32_t size;    // size of arrays term_of and val (nvars <= size)
  uint32_t esize;   // size of arrays cnstr and score (nelims <= esize)

  // data for all variables
  term_t *term_of;
  rational_t *val;

  // additional data for the variables to eliminate
  ptr_set_t **cnstr;
  aproj_score_t *score;

  // reverse mapping: term id to var
  int_hmap_t tmap;
} aproj_vtbl_t;


#define MAX_APROJ_VTBL_SIZE (UINT32_MAX/sizeof(aproj_score_t))
#define DEF_APROJ_VTBL_SIZE 20
#define DEF_APROJ_VTBL_ESIZE 20


/*
 * Projector data structure:
 * - pointers to the relevant term table and term manager
 * - table of variables
 * - set of all constraints
 * - auxiliary buffers for polynomial operations
 */
typedef struct arith_projector_s {
  term_table_t *terms;
  term_manager_t *manager;
  aproj_vtbl_t vtbl;
  ptr_set_t *constraints;
  poly_buffer_t buffer;
  rational_t q1, q2;
} arith_projector_t;





/*
 * Initialize projector
 * - mngr = relevant term manager
 * - n = initial size (total number of variables)
 * - m = initial esize (number of variables to eliminate)
 * - m must be no more than m
 *
 * Parameters n and m specify the initial size and esize
 * - if n is 0, the default size and esize are used (m should be 0 too)
 * - if n>0 and m=0, the initial size is n and the initial esize is
 *   min(n, default esize).
 */
extern void init_arith_projector(arith_projector_t *proj, term_manager_t *mngr, uint32_t n, uint32_t m);


/*
 * Reset:
 * - remove all variables and constraints
 * - reset all internal tables.
 */
extern void reset_arith_projector(arith_projector_t *proj);


/*
 * Delete: free memory
 */
extern void delete_arith_projector(arith_projector_t *proj);


/*
 * Add variable x
 * - x must be a valid term index in proj->terms
 * - x must be distinct from all previously added variables
 * - if to_elim is true then x is a marked as a variable to 
 *   eliminate, otherwise x is a variable to keep
 * - q = value of x in the model
 * - proj must not have any constraints: all variables must be
 *   declared before the first call to aproj_add_constraint 
 */
extern void aproj_add_var(arith_projector_t *proj, term_t x, bool to_elim, rational_t *q);


/*
 * Add constraint c
 * - c must be an arithmetic predicate of the following forms
 *    (ARITH_EQ_ATOM t)
 *    (ARITH_BINEQ_ATOM t1 t2)
 *    (ARITH_GE_ATOM t)
 *    (NOT (ARITH_GE_ATOM t))
 *   where t, t1, t2 are either variables declared in proj or linear
 *   polynomials in variables declared in proj
 * - c must be true in the model specified by calls to aproj_add_var
 * - no variables can be added after this function is called
 */
extern void aproj_add_constraint(arith_projector_t *proj, term_t c);


/*
 * Apply the variable elimination procedure
 * - no variable or constraint can be added after this function is called.
 */
extern void aproj_eliminate(arith_projector_t *proj);


/*
 * Collect the result as a formula:
 * - returns either true_term or a conjunction of arithmetic constraints
 *   that do not contain the eliminated variables.
 */
extern term_t aproj_get_formula(arith_projector_t *proj);



#endif /* __ARITH_PROJECTION_H */
