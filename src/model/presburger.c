/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * COOPER/PRESBURGER PLAYGROUND
 */
#include <assert.h>

#include "model/presburger.h"


//Currently relying on the parser or literal collector or (?) to enforce the presburger conditions on
//multiplications.
bool is_presburger_literal(term_table_t *terms, term_t t) {
  bool retval;
  term_t u, k; 
  composite_term_t *args;
  
  switch (term_kind(terms, t)) {

  case ARITH_EQ_ATOM:           //(u = 0)
    u = arith_eq_arg(terms, t);
    retval = is_integer_term(terms, u);
    break;

  case ARITH_GE_ATOM:           //(u >= 0)   
    u = arith_ge_arg(terms, t);
    retval = is_integer_term(terms, u);
    break;
    
  case ARITH_BINEQ_ATOM:        //(u0 = u1)
    args = arith_bineq_atom_desc(terms, t);
    retval = is_integer_term(terms, args->arg[0]) && is_integer_term(terms, args->arg[1]);
    break;
    
  case ARITH_DIVIDES_ATOM:      //(k | u)
    args = arith_divides_atom_desc(terms, t);
    k = args->arg[0];
    u = args->arg[1];
    retval = is_constant_term(terms, k) && is_integer_term(terms, k) && is_integer_term(terms, u);
    break;

  default:
    retval = false;
  }
  
  return retval;
}



/*
 * Initialize proj
 * - mngr = relevant term manager
 * - n = initial size (total number of variables)
 * - m = initial esize (number of variables to eliminate)
 * - n must be no more than m
 *
 */
void init_presburger_projector(presburger_t *proj, term_manager_t *mngr, uint32_t n, uint32_t m) {
  proj->terms = term_manager_get_terms(mngr);
  proj->manager = mngr;

}


/*
 * Reset:
 */
void reset_presburger_projector(presburger_t *proj) {


}


/*
 * Delete: free memory
 */
void delete_presburger_projector(presburger_t *proj) {


}



void presburger_add_var(presburger_t *pres, term_t x, bool to_elim, rational_t *q){


}


int32_t presburger_add_constraint(presburger_t *pres, term_t c){

  return 0;
}


/*
 * Apply the variable elimination procedure
 * - no variable or constraint can be added after this function is called.
 */
void presburger_eliminate(presburger_t *pres){


}



/*
 * Collect the result as a vector of formulas
 * - every constraint in proj->constraint is converted to a Boolean
 *   term that's added to vector v
 * - v is not reset
 *
 * So the set of constraints after in proj->constraint is equivalent to 
 * the conjunction of formulas added to v.
 */
void presburger_get_formula_vector(presburger_t *pres, ivector_t *v){


}


/*
 * Collect the result as a formula:
 * - returns either true_term or a conjunction of arithmetic constraints
 *   that do not contain the eliminated variables.
 */
term_t presburger_get_formula(presburger_t *pres){
  ivector_t v;
  term_t t;

  init_ivector(&v, 10);
  presburger_get_formula_vector(pres, &v);
  t = mk_and(pres->manager, v.size, v.data);
  delete_ivector(&v);

  return t;
}





