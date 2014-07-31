/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * VARIABLE ELIMINATION BY SUBSTITUTION
 */

#include <assert.h>

#include "terms/elim_subst.h"


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
  init_ivector(&subst->aux, 0);
}

/*
 * Delete the whole thing
 */
void delete_elim_subst(elim_subst_t *subst) {
  delete_full_subst(&subst->full_subst);
  delete_ivector(&subst->aux);
}


/*
 * CONVERT ATOMS TO SUBSTITUTION MAPS
 */

/*
 * Test whether x is an elimination candidate:
 * - x must be UNINTERPRETED_TERM
 * - return true if x is in the elimvar set
 *   and is not mapped to anything in subst->full_subst.
 */
static bool is_elim_candidate(elim_subst_t *subst, term_t x) {
  assert(is_pos_term(x) && term_kind(subst->terms, x) == UNINTERPRETED_TERM);

  return int_hset_member(subst->elimvars, x)
    && !full_subst_is_mapped(&subst->full_subst, x);
}


/*
 * Check whether the map [x --> t] can be added to full_subst
 * - x must be an uninterpreted term
 * - if check_cycles is false, this just checks whether x is an elimination
 *   candidate. If check_cycles is true, this also check whether the map
 *   would cause a substitution cycle.
 */
static bool test_elim_map(elim_subst_t *subst, term_t x, term_t t, bool check_cycles) {
  assert(is_pos_term(x) && term_kind(subst->terms, x) == UNINTERPRETED_TERM);

  if (check_cycles) {
    return int_hset_member(subst->elimvars, x)
      && full_subst_check_map(&subst->full_subst, x, t);
  } else {
    return is_elim_candidate(subst, x);
  }
}

/*
 * All functions below try to convert an equality into a substitution map.
 * If the flag check_cycles is true, a map is accepted only if it doesn't create
 * a substitution cycle.
 */

/*
 * Check whether any variable of p other than x depends on x
 */
static bool arith_elim_causes_cycle(elim_subst_t *subst, polynomial_t *p, term_t x) {
  ivector_t *v;
  uint32_t i, n;
  term_t y;

  v = &subst->aux;
  ivector_reset(v);

  n = p->nterms;
  i = 0;
  if (p->mono[i].var == const_idx) {
    i ++; // skip the constant
  }
  while (i<n) {
    y = p->mono[i].var;
    if (y != x) {
      ivector_push(v, y);
    }
    i ++;
  }

  return full_subst_check_deps(&subst->full_subst, x, v->size, v->data);
}

/*
 * Atom p == 0 where p is a polyomial:
 * - we search for a variable y to eliminate from p then rewrite p == 0 to y == q
 */
static bool elim_subst_try_arith_elim(elim_subst_t *subst, polynomial_t *p, bool check_cycles) {
  uint32_t i, n;
  term_t x, q;

  n = p->nterms;
  i = 0;
  if (p->mono[i].var == const_idx) {
    // skip the constant
    i ++;
  }

  while (i < n) {
    x = p->mono[i].var;
    if (is_elim_candidate(subst, x)) {
      if (!check_cycles || !arith_elim_causes_cycle(subst, p, x)) {
	// success: add the map [x --> q] for q = elim of x in p
	q = mk_arith_elim_poly(subst->mngr, p, x);
	full_subst_add_map(&subst->full_subst, x, q);
	return true;
      }
    }
    i ++;
  }

  return false;
}

/*
 * Atom (t == 0) where t is an arithmetic term
 */
static bool elim_subst_try_arith_eq0(elim_subst_t *subst, term_t t, bool check_cycles) {
  assert(is_pos_term(t));

  switch (term_kind(subst->terms, t)) {
  case UNINTERPRETED_TERM:
    if (test_elim_map(subst, t, zero_term, check_cycles)) {
      full_subst_add_map(&subst->full_subst, t, zero_term);
      return true;
    }
    break;

  case ARITH_POLY:
    return elim_subst_try_arith_elim(subst, poly_term_desc(subst->terms, t), check_cycles);

  default:
    break;
  }

  return false;
}


/*
 * Atom (t1 == t2) for non-Boolean terms t1 and t2
 */
static bool elim_subst_try_eq(elim_subst_t *subst, term_t t1, term_t t2, bool check_cycles) {
  assert(is_pos_term(t1) && is_pos_term(t2));

  if (term_kind(subst->terms, t1) == UNINTERPRETED_TERM &&
      test_elim_map(subst, t1, t2, check_cycles)) {
    // map [t1 --> t2]
    full_subst_add_map(&subst->full_subst, t1, t2);
    return true;
  }

  if (term_kind(subst->terms, t2) == UNINTERPRETED_TERM &&
      test_elim_map(subst, t1, t2, check_cycles)) {
    // map [t2 --> t1]
    full_subst_add_map(&subst->full_subst, t2, t1);
    return true;
  }

  return false;
}

/*
 * Atom (t1 == t2) for two Boolean terms t1 and t2
 */
static bool elim_subst_try_booleq(elim_subst_t *subst, term_t t1, term_t t2, bool check_cycles) {
  if (term_kind(subst->terms, t1) == UNINTERPRETED_TERM) {
    if (is_neg_term(t1)) {
      // rewrite to (not t1) == (not t2)
      t1 = opposite_term(t1);
      t2 = opposite_term(t2);
    }
    if (test_elim_map(subst, t1, t2, check_cycles)) {
      // map [t1 --> t2]
      full_subst_add_map(&subst->full_subst, t1, t2);
      return true;
    }
  }

  if (term_kind(subst->terms, t2) == UNINTERPRETED_TERM) {
    if (is_neg_term(t2)) {
      t2 = opposite_term(t2);
      t1 = opposite_term(t1);
    }
    if (test_elim_map(subst, t2, t1, check_cycles)) {
      // map [t2 --> t1];
      full_subst_add_map(&subst->full_subst, t2, t1);
      return true;
    }
  }

  return false;
}


/*
 * Literal f (either t or not t, where t is UNINTERPRETED_TERM)
 */
static bool elim_subst_try_prop_variable(elim_subst_t *subst, term_t f) {
  term_t u;

  assert(term_kind(subst->terms, f) == UNINTERPRETED_TERM);

  u = true_term;
  if (is_neg_term(f)) {
    // rewrite to (not f) == false
    f = opposite_term(f);
    u = false_term;
  }

  /*
   * Since u is a constant, the substitution [f := u] can't cause
   * a cycle. We just check whether f is an elimination candidate.
   */
  if (is_elim_candidate(subst, f)) {
    full_subst_add_map(&subst->full_subst, f, u);
    return true;
  }

  return false;
}


/*
 * Check whether f is equivalent to an equality (y == t)
 * where y is a candidate for elimination.
 * - if so, add map [y --> t] to the internal full_subst and return true
 * - otherwise, do nothing and return false.
 */
bool elim_subst_try_map(elim_subst_t *subst, term_t f, bool check_cycles) {
  term_table_t *terms;
  composite_term_t *eq;
  bool result;
  term_t t1, t2;

  result = false;
  terms = subst->terms;
  switch (term_kind(terms, f)) {
  case UNINTERPRETED_TERM:
    if (is_boolean_term(terms, f)) {
      result = elim_subst_try_prop_variable(subst, f);
    }
    break;

  case ARITH_EQ_ATOM: // (t == 0)
    if (is_pos_term(f)) {
      t1 = arith_eq_arg(terms, f);
      result = elim_subst_try_arith_eq0(subst, t1, check_cycles);
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
      result = elim_subst_try_booleq(subst, t1, t2, check_cycles);
    } else if (is_pos_term(f)) {
      result = elim_subst_try_eq(subst, t1, t2, check_cycles);
    }
    break;

  case ARITH_BINEQ_ATOM: // (t1 == t2): two arithemtic terms
  case BV_EQ_ATOM:       // (t1 == t2): two bitvector terms
    if (is_pos_term(f)) {
      eq = composite_term_desc(terms, f);
      assert(eq->arity == 2);
      t1 = eq->arg[0];
      t2 = eq->arg[1];
      result = elim_subst_try_eq(subst, t1, t2, check_cycles);
    }
    break;

  default:
    break;
  }

  return result;
}

