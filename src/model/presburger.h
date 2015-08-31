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
#include "terms/poly_buffer.h"

#include "utils/ptr_vectors.h"
#include "utils/int_hash_sets.h"


/*
 * Tags for identifying the constraint types
 *   PRES_GT           = 0       strict inequality (poly > 0)
 *   PRES_GE           = 1       non-strict inequality  (poly >= 0)
 *   PRES_EQ           = 2       equality   (poly = 0)
 *   PRES_POS_DIVIDES  = 3       divides    + (k | poly)
 *   PRES_NEG_DIVIDES  = 4       divides    - (k | poly)
 *
 */
typedef enum {
  PRES_GT           = 0,
  PRES_GE           = 1,
  PRES_EQ           = 2,
  PRES_POS_DIVIDES  = 3,
  PRES_NEG_DIVIDES  = 4,
} presburger_tag_t;

/*
 * Tags for identifying the Cooper form of a constraint.
 *
 *  VAR_LT   y < e
 *  VAR_GT   e < y
 *  VAR_EQ   y = e
 *  VAR_PD   d | y + r
 *  VAR_ND   not (d | y + r)
 *
 */
typedef enum {
  VAR_NONE = -1,
  VAR_LT   =  0,
  VAR_GT   =  1,
  VAR_EQ   =  2,
  VAR_DV   =  3,
} cooper_tag_t;

/*
 * In the elimination of y we keep track of:
 * - lub, the (strict) least upper bound on y
 * - lubv, the value of the lub in the model
 * - glb, the (strict) greatest lower bound on y
 * - glbv, the value of the blb in the model
 * - poly, and exact solution "y = poly" if there is such a constraint
 * - delta, the lcm of all the (in)divisibility constraints.
 */
typedef struct cooper_s {
  //the greatest lower bound and its value
  polynomial_t *glb;
  rational_t glbv;
  //the least upper bound and its value
  polynomial_t *lub;
  rational_t lubv;
  //an exact solution if we have one
  polynomial_t *poly;
  //the lcm of the divides constants
  rational_t delta;
} cooper_t;


/*
 * Presburger constraint:
 * - id = constraint id (it's index in the constraints pvector)
 * - tag = constraint type
 * - nterms = number of monomials
 * - mono = array of nterms + 1 monomials
 * we use the same conventions as in polynomials.h:
 * - the monomials are ordered by increasing variable index
 * - mono[nterms] contains the end marker max_idx
 * - const_idx = 0 denotes the constant
 * - divisor; used if the constraint is a divides ±(k | u)
 *   stores the value of k
 *
 * - the id is a counter incremented with every new constraint
 */
typedef struct presburger_constraint_s {
  uint32_t id;
  presburger_tag_t tag;
  uint32_t nterms;
  rational_t *divisor;  // non-null only when tag is either PRES_POS_DIVIDES, or  PRES_NEG_DIVIDES.
  monomial_t mono[0];   // real size = nterms+1
} presburger_constraint_t;

#define MAX_PRESBURGER_CONSTRAINT_SIZE (((UINT32_MAX-sizeof(presburger_constraint_t))/sizeof(monomial_t)) - 1)

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
 * An impoverished version Bruno's arith_proj vtbl.
 *
 */
typedef struct presburger_vtbl_s {
  uint32_t nvars;   // number of variables
  uint32_t nelims;  // variables to eliminate
  uint32_t size;    // size of arrays variables and values (nvars <= size)

  // the variables we are going to eliminate
  ivector_t eliminables;
  int_hset_t elims;

  // data for *all* variables (both to_elim and to_keep)
  term_t *variables;
  rational_t *values;

  // mapping a variable to its index in the variables array
  // which should also be the index of it's value in the values
  // array
  int_hmap_t vmap;
} presburger_vtbl_t;


#define MAX_PRESBURGER_VTBL_SIZE (UINT32_MAX/sizeof(presburger_vtbl_t))   
#define DEF_PRESBURGER_VTBL_SIZE 20


/*
 * Presburger projector data structure:
 * - pointers to the relevant term table and term manager
 */
typedef struct presburger_s {
  term_table_t *terms;
  term_manager_t *manager;
  presburger_vtbl_t vtbl;
  pvector_t constraints;
  // buffers
  poly_buffer_t buffer;
} presburger_t;

/*
 * Check that the term in question is indeed a presburger literal.
 * The most likely reason this would fail is that the term contained
 * Real variables or constants.
 */
extern bool is_presburger_literal(term_table_t *table, term_t t);

/*
 * Initialize projector
 * - mngr = relevant term manager
 * - n = initial size (total number of variables)
 * - c = number of constraints
 */
extern void init_presburger_projector(presburger_t *pres, term_manager_t *mngr, uint32_t n, uint32_t c);


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
 * Close the set of variables and prepare for addition of constraints.
 * - this function must be called once all variables have been added
 *   and before adding the first constraint.
 */
extern void presburger_close_var_set(presburger_t *pres);


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
 *   polynomials in variables declared in proj, and k is an integer constant.
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
 *   are rejected with error code NOT_PRESBURGER_LITERAL, even if t1 ... t_n
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
