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


/*
 * Build and add a constraint
 * - convert term ids to internal variables
 */
// constraint t == 0
static void presburger_add_var_eq_zero(presburger_t *pres, term_t t) {
  /*
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_add_var(buffer, &proj->vtbl, t);
  add_constraint_from_buffer(proj, buffer, APROJ_EQ);
  */
}

// constraint t >= 0
static void presburger_add_var_geq_zero(presburger_t *pres, term_t t) {
  /*
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_add_var(buffer, &proj->vtbl, t);
  add_constraint_from_buffer(proj, buffer, APROJ_GE);
  */
}

// constraint t < 0 (converted to -t > 0)
static void presburger_add_var_lt_zero(presburger_t *pres, term_t t) {
  /*
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_sub_var(buffer, &proj->vtbl, t);
  add_constraint_from_buffer(proj, buffer, APROJ_GT);
  */
}

// constraint p == 0
static void presburger_add_poly_eq_zero(presburger_t *pres, polynomial_t *p) {
  /*
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_add_poly(buffer, &proj->vtbl, p);
  add_constraint_from_buffer(proj, buffer, APROJ_EQ);
  */
}

// constraint p >= 0
static void presburger_add_poly_geq_zero(presburger_t *pres, polynomial_t *p) {
  /*
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_add_poly(buffer, &proj->vtbl, p);
  add_constraint_from_buffer(proj, buffer, APROJ_GE);
  */
}

// constraint p < 0 (converted to -p > 0)
static void presburger_add_poly_lt_zero(presburger_t *pres, polynomial_t *p) {
  /*
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_sub_poly(buffer, &proj->vtbl, p);
  add_constraint_from_buffer(proj, buffer, APROJ_GT);
  */
}


// constraint (eq t1 t2)
static void presburger_add_arith_bineq(presburger_t *pres, composite_term_t *eq) {
  /*
  poly_buffer_t *buffer;
  term_table_t *terms;
  term_t t1, t2;

  assert(eq->arity == 2);
  t1 = eq->arg[0];
  t2 = eq->arg[1];

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  terms = proj->terms;
  switch (term_kind(terms, t1)) {
  case ARITH_CONSTANT:    
    poly_buffer_add_const(buffer, rational_term_desc(terms, t1));
    break;

  case ARITH_POLY:
    aproj_buffer_add_poly(buffer, &proj->vtbl, poly_term_desc(terms, t1));
    break;

  default:
    aproj_buffer_add_var(buffer, &proj->vtbl, t1);
    break;
  }

  switch (term_kind(terms, t2)) {
  case ARITH_CONSTANT:    
    poly_buffer_sub_const(buffer, rational_term_desc(terms, t2));
    break;

  case ARITH_POLY:
    aproj_buffer_sub_poly(buffer, &proj->vtbl, poly_term_desc(terms, t2));
    break;

  default:
    aproj_buffer_sub_var(buffer, &proj->vtbl, t2);
    break;
  }
  add_constraint_from_buffer(proj, buffer, APROJ_EQ);
  */
}

// constraint (t1 | t2) 
static void presburger_add_arith_divides(presburger_t *pres, composite_term_t *eq, bool positive) {


}

/*
 * Add constraint c
 * - c must be an arithmetic predicate of the following forms
 *    (ARITH_EQ_ATOM t)
 *    (ARITH_BINEQ_ATOM t1 t2)
 *    (ARITH_GE_ATOM t)
 *    (NOT (ARITH_GE_ATOM t))
 *    (ARITH_DIVIDES_ATOM k t)
 *    (NOT (ARITH_DIVIDES_ATOM k t))
 *   where t, t1, t2 are either variables declared in proj or linear
 *   polynomials in variables declared in proj, and k is an integer constant.
 * - c must be true in the model specified by calls to aproj_add_var
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
 */

int32_t presburger_add_constraint(presburger_t *pres, term_t c) {
  term_table_t *terms;
  term_t t;
  int32_t code;

  terms = pres->terms;

  assert(good_term(terms, c) && is_boolean_term(terms, c));

  code = 0;
  switch (term_kind(terms, c)) {
  case CONSTANT_TERM:
    // c is either true_term or false_term
    // for true_term, we do nothing
    // for false_term we return an error code.
    if (c == false_term) {
      code = PRES_ERROR_FALSE_LITERAL;
    }
    break;

  case ARITH_EQ_ATOM:
    if (is_neg_term(c)) {
      code = PRES_ERROR_ARITH_DISEQ;
    } else {
      t = arith_eq_arg(terms, c);
      if (term_kind(terms, t) == ARITH_POLY) {
	presburger_add_poly_eq_zero(pres, poly_term_desc(terms, t));
      } else {
	presburger_add_var_eq_zero(pres, t);
      }
    }
    break;

  case ARITH_BINEQ_ATOM:
    if (is_neg_term(c)) {
      code = PRES_ERROR_ARITH_DISEQ;
    } else {
      presburger_add_arith_bineq(pres, arith_bineq_atom_desc(terms, c));
    }
    break;

  case ARITH_GE_ATOM:
    t = arith_ge_arg(terms, c);    
    if (is_pos_term(c)) {
      // atom (t >= 0)
      if (term_kind(terms, t) == ARITH_POLY) {
	presburger_add_poly_geq_zero(pres, poly_term_desc(terms, t));
      } else {
	presburger_add_var_geq_zero(pres, t);
      }
    } else {
      // atom (t < 0)
      if (term_kind(terms, t) == ARITH_POLY) {
	presburger_add_poly_lt_zero(pres, poly_term_desc(terms, t));
      } else {
	presburger_add_var_lt_zero(pres, t);
      }
    }
    break;

  case ARITH_DIVIDES_ATOM:
    if (is_neg_term(c)) {
      presburger_add_arith_divides(pres, arith_bineq_atom_desc(terms, c), false);
    } else {
      presburger_add_arith_divides(pres, arith_bineq_atom_desc(terms, c), true);
    }
    break;

    
  default:
    code = PRES_ERROR_NOT_PRESBURGER_LITERAL;
    break;
  }

  return code;
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





