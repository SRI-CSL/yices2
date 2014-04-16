/*
 * VARIABLE ELIMINATION BY SUBSTITUTION
 */

#include <assert.h>

#include "elim_subst.h"


/*
 * Initialize:
 * - mngr = term_manager
 * - elimvars = set of candidate for elimination
 */
void init_elim_subst(elim_subst_t *subst, term_manager_t *mngr, int_hset_t *elimvars) {
  subst->mngr = mngr;
  subst->terms = term_manager_get_terms(mngr);
  subst->elimvars = elimvars;
  init_full_subst(&subst->full_subst, mngr);
}

/*
 * Delete the whole thing
 */
void delete_elim_subst(elim_subst_t *subst) {
  delete_full_subst(&subst->full_subst);
}


/*
 * CONVERT ATOMS TO SUBSTITUTION MAPS
 */

/*
 * Atom (t == 0) where t is an arithmetic term
 */
static bool elim_subst_try_arith_eq0(elim_subst_t *subst, term_t t) {
  return false; // TBD
}

/*
 * Atom (t1 == t2) for non-Boolean terms t1 and t2
 */
static bool elim_subst_try_eq(elim_subst_t *subst, term_t t1, term_t t2) {
  return false; // TBD
}

/*
 * Atom (t1 == t2) for two Boolean terms t1 and t2
 */
static bool elim_subst_try_booleq(elim_subst_t *subst, term_t t1, term_t t2) {
  return false; // TBD
}


/*
 * Check whether f is equivalent to an equality (y == t)
 * where y is a candidate for elimination.
 * - if so, add map [y --> t] to the internal full_subst and return true
 * - otherwise, do nothing and return false.
 */
bool elim_subst_try_map(elim_subst_t *subst, term_t f) {
  term_table_t *terms;
  composite_term_t *eq;
  bool result;
  term_t t1, t2;

  result = false;
  terms = subst->terms;
  switch (term_kind(terms, f)) {
  case ARITH_EQ_ATOM: // (t == 0)
    if (is_pos_term(f)) {
      t1 = arith_eq_arg(terms, f);
      result = elim_subst_try_arith_eq0(subst, t1);
    }
    break;

  case EQ_TERM: // (t1 == t2)
    eq = eq_term_desc(terms, f);
    assert(eq->arity == 2);
    t1 = eq->arg[0];
    t2 = eq->arg[1];
    if (is_boolean_term(terms, t1)) {
      // if f is (not (eq t1 t2)), we rewrite it to (eq (not t1) t2)
      if (is_neg_term(f)) {
	t1 = opposite_term(t1);
      }
      result = elim_subst_try_booleq(subst, t1, t2);
    } else if (is_pos_term(f)) {
      result = elim_subst_try_eq(subst, t1, t2);
    }
    break;

  case ARITH_BINEQ_ATOM: // (t1 == t2): two arithemtic terms
  case BV_EQ_ATOM:       // (t1 == t2): two bitvector terms
    if (is_pos_term(f)) {
      eq = composite_term_desc(terms, f);
      assert(eq->arity == 2);
      t1 = eq->arg[0];
      t2 = eq->arg[1];
      result = elim_subst_try_eq(subst, t1, t2);
    }
    break;

  default:
    break;
  }

  return result;
}

/*
 * Same thing but also check whether [y --> t] causes a substitution cycle
 * - if there's a cycle, the map is not added and the function returns false
 */
bool elim_subst_try_check_map(elim_subst_t *subst, term_t f) {
  return false;   // TBD
}
