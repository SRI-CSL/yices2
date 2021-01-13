/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * SUPPORT FOR COMPUTING IMPLICANTS
 */

/*
 * Given a model M and a formula f such that M satisfies f, we want to
 * compute an implicant for f. The implicant is a set/conjunction of
 * literals p_1 .... p_n such that:
 *  1) every p_i is true in M
 *  2) p_1 /\ p_2 /\ ... /\ p_n => f (is valid)
 *
 *
 * To deal with if-then-else, we generalize the problem as follows:
 * - given a model M and a term t, collect a set of literals
 *   p_1 .... p_n and a term u such that
 *   1) every p_i is true in M
 *   2) p_1 /\ p_2 /\ ... /\ p_n => (t == u)
 *   3) u is atomic:
 *      if t is Boolean, u is either true_term or false_term
 *      otherwise u a term with no if-then-else subterms
 *      (e.g., u is an arithmetic term with no if-then-else).
 *
 * - informally, u is the result of simplifying t modulo p_1 ... p_n
 * - example:
 *   processing  2 + (ite (< x y) x y) may return
 *    literal: (< x y)
 *    simplified term: 2 + x
 *    if (< x y) is true in M
 *
 * Then to get the implicant for a formula f, we process f, the simplified
 * term should be true and the set of literals collected imply f.
 *
 */

#include <stdbool.h>

#include "model/literal_collector.h"
#include "utils/int_array_sort2.h"

#ifdef HAVE_MCSAT
#include <poly/algebraic_number.h>
#endif


/*
 * Initialization: prepare collector for model mdl
 * - collect->env is not touched.
 */
void init_lit_collector(lit_collector_t *collect, model_t *mdl, term_manager_t *mngr) {
  assert(term_manager_get_terms(mngr) == mdl->terms);

  collect->terms = mdl->terms;
  collect->manager = mngr;
  collect->model = mdl;
  init_evaluator(&collect->eval, mdl);
  init_int_hmap(&collect->tcache, 0);
  init_int_hmap(&collect->fcache, 0);
  init_int_hset(&collect->lit_set, 0);
  init_istack(&collect->stack);
  collect->options = LIT_COLLECTOR_DEFAULT_OPTIONS;
  collect->bool_are_terms = false;
}


/*
 * Delete everything
 */
void delete_lit_collector(lit_collector_t *collect) {
  delete_evaluator(&collect->eval);
  delete_int_hmap(&collect->tcache);
  delete_int_hmap(&collect->fcache);
  delete_int_hset(&collect->lit_set);
  delete_istack(&collect->stack);
}


/*
 * Reset: empty the lit_set and the caches
 */
void reset_lit_collector(lit_collector_t *collect) {
  int_hmap_reset(&collect->tcache);
  int_hmap_reset(&collect->fcache);
  int_hset_reset(&collect->lit_set);
  reset_istack(&collect->stack);
}


/*
 * Get the term mapped to t in collect->tcache or collect->fcache
 * - return NULL_TERM if t is not in the cache
 */
static term_t lit_collector_find_cached_term(lit_collector_t *collect, term_t t) {
  int_hmap_t *cache;
  int_hmap_pair_t *r;
  term_t u;

  assert(good_term(collect->terms, t));

  cache = &collect->tcache; // default cache for terms
  if (is_boolean_term(collect->terms, t) && !collect->bool_are_terms) {
    // t is visited as a formula: use the fcache
    cache = &collect->fcache;
  }

  u = NULL_TERM;
  r = int_hmap_find(cache, t);
  if (r != NULL) {
    u = r->val;
    assert(good_term(collect->terms, u));
  }

  return u;
}


/*
 * Store the mapping t --> u in the relevant cache
 */
static void lit_collector_cache_result(lit_collector_t *collect, term_t t, term_t u) {
  int_hmap_t *cache;
  int_hmap_pair_t *r;

  assert(good_term(collect->terms, t) && good_term(collect->terms, u));

  cache = &collect->tcache; // default cache
  if (is_boolean_term(collect->terms, t) && !collect->bool_are_terms) {
    cache = &collect->fcache; // formula cache
  }

  r = int_hmap_get(cache, t);
  assert(r != NULL && r->val == -1);
  r->val = u;
}



/*
 * Evaluate t: raise an exception if the evaluation fails
 */
static value_t lit_collector_eval(lit_collector_t *collect, term_t t) {
  value_t v;

  v = eval_in_model(&collect->eval, t);
  if (v < 0) {
    fprintf(stderr, "ERROR!!!\n");
    longjmp(collect->env, v);
  }
  return v;
}

/*
 * Check whether t is true in the model
 * - t must be a Boolean term
 */
static bool term_is_true_in_model(lit_collector_t *collect, term_t t) {
  value_t v;

  assert(is_boolean_term(collect->terms, t));

  v = lit_collector_eval(collect, t);

  return is_true(&collect->model->vtbl, v);
}

/*
 * Check whether t is false
 */
static bool term_is_false_in_model(lit_collector_t *collect, term_t t) {
  value_t v;

  assert(is_boolean_term(collect->terms, t));

  v = lit_collector_eval(collect, t);

  return is_false(&collect->model->vtbl, v);
}


/*
 * Variant: for debugging
 */
#ifndef NDEBUG
static bool is_true_in_model(lit_collector_t *collect, term_t t) {
  value_t v;

  assert(is_boolean_term(collect->terms, t));
  v = eval_in_model(&collect->eval, t);
  return is_true(&collect->model->vtbl, v);
}
#endif




/*
 * SUPPORT FOR PROCESSING OF ARITHMETIC ATOMS
 */

/*
 * Compare the values of t1 and t2 in the model
 * - both t1 and t2 must be arithmetic terms
 * - return code:
 *   a negative number if value(t1) < value(t2)
 *   zero if value(t1) = value(t2)
 *   a positive number if value(t1) > value(t2)
 */
static int arith_cmp_in_model(lit_collector_t *collect, term_t t1, term_t t2) {
  value_table_t *vtbl;
  value_t v1, v2;

  assert(is_arithmetic_term(collect->terms, t1) &&
	 is_arithmetic_term(collect->terms, t2));

  v1 = lit_collector_eval(collect, t1);
  v2 = lit_collector_eval(collect, t2);
  vtbl = &collect->model->vtbl;
  return q_cmp(vtbl_rational(vtbl, v1), vtbl_rational(vtbl, v2));
}


/*
 * Get the sign of t in the model
 * - t must be an arithmetic term
 * - return 0 if value(t) is 0
 * - return +1 if value(t) is positive
 * - return -1 if value(t) is negative
 */
static int lit_collector_sign_in_model(lit_collector_t *collect, term_t t) {
  value_t v;

  assert(is_arithmetic_term(collect->terms, t));

  v = lit_collector_eval(collect, t);
  if (object_is_rational(&collect->model->vtbl, v)) {
    return q_sgn(vtbl_rational(&collect->model->vtbl, v));
  } else {
    return lp_algebraic_number_sgn(vtbl_algebraic_number(&collect->model->vtbl, v));
  }
}


/*
 * Sort the terms of a in increasing order:
 * - n = size of a
 * - all elements in a must be arithmetic terms
 * - the ordering is: t1 < t2 if value of t1 < value of t2 in the model
 */
static bool lt_in_model(void *d, term_t t1, term_t t2) {
  return arith_cmp_in_model(d, t1, t2) < 0;
}

static void lit_collector_sort_in_model(lit_collector_t *collect, uint32_t n, term_t *a) {
  int_array_sort2(a, n, collect, lt_in_model);
}


/*
 * FOR NOT DISTINCT
 */

/*
 * Sort the elements of a (to detect whether two of them are equal)
 * - the ordering is based on the value index
 *
 * There's some overhead since we may evaluate the same term several
 * times. Since the evaluator uses a cache, this overhead should be
 * small.
 */
static bool lt_in_model2(void *d, term_t t1, term_t t2) {
  value_t v1, v2;

  v1 = lit_collector_eval(d, t1);
  v2 = lit_collector_eval(d, t2);
  return v1 < v2;
}

static void lit_collector_sort_by_value(lit_collector_t *collect, uint32_t n, term_t *a) {
  int_array_sort2(a, n, collect, lt_in_model2);
}

/*
 * Check whether t1 and t2 have the same value
 */
static bool equal_in_model(lit_collector_t *collect, term_t t1, term_t t2) {
  value_t v1, v2;

  v1 = lit_collector_eval(collect, t1);
  v2 = lit_collector_eval(collect, t2);
  return v1 == v2;
}



/*
 * ADDITION OF LITERALS
 */

/*
 * Add t to the set of literals
 * - t must be a true in the model
 * - do nothing it t is true_term
 */
static void lit_collector_add_literal(lit_collector_t *collect, term_t t) {
  assert(is_true_in_model(collect, t));
  if (t != true_term) {
    (void) int_hset_add(&collect->lit_set, t);
  }
}

/*
 * Check whether t is a simple term
 */
static bool simple_bool_term(lit_collector_t *collect, term_t t) {
  bool result;

  switch (term_kind(collect->terms, t)) {
  case UNINTERPRETED_TERM:
  case APP_TERM:
  case SELECT_TERM:
  case BIT_TERM:
    result = true;
    break;

  default:
    result = false;
    break;
  }

  return result;
}


/*
 * Found an atom t:
 * - if collect->bool_are_terms is true and t is simple, we do nothing and return t
 * - otherwise we add either t or not(t) to the set of literals
 *   and we return true_term or false_term (i.e., value of t in the model)
 */
static term_t register_atom(lit_collector_t *collect, term_t t) {
  term_t u;

  if (collect->bool_are_terms && simple_bool_term(collect, t)) {
    return t;
  }

  u = true_term;
  if (! term_is_true_in_model(collect, t)) {
    u = false_term;
    t = opposite_term(t);
  }
  lit_collector_add_literal(collect, t);

  return u;
}


/*
 * RECURSIVE PROCESSING
 */

/*
 * Test equality of two arrays of terms
 */
static bool inequal_arrays(term_t *a, term_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] != b[i]) return true;
  }
  return false;
}


/*
 * Variant for pprod: check whether a[i] != p->prod[i].var for some i
 * - a must have the same size as p (i.e., p->len)
 */
static bool inequal_array_pprod(term_t *a, pprod_t *p) {
  uint32_t i, n;

  n = p->len;
  for (i=0; i<n; i++) {
    if (a[i] != p->prod[i].var) return true;
  }
  return false;
}


/*
 * Variants for polynomials
 */
static bool inequal_array_poly(term_t *a, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  for (i=0; i<n; i++) {
    if (a[i] != p->mono[i].var) return true;
  }

  return false;
}

static bool inequal_array_bvpoly64(term_t *a, bvpoly64_t *p) {
  uint32_t i, n;

  n = p->nterms;
  for (i=0; i<n; i++) {
    if (a[i] != p->mono[i].var) return true;
  }

  return false;
}

static bool inequal_array_bvpoly(term_t *a, bvpoly_t *p) {
  uint32_t i, n;

  n = p->nterms;
  for (i=0; i<n; i++) {
    if (a[i] != p->mono[i].var) return true;
  }

  return false;
}



/*
 * Process a term t: collect literals of t and return an atomic term
 * equal to t modulo the literals.
 * - if collect->bool_are_terms is true then Boolean terms are treated as ordinary terms
 */
static term_t lit_collector_visit(lit_collector_t *collect, term_t t);


/*
 * Process t (preserve Boolean terms)
 */
static term_t lit_collector_visit_term(lit_collector_t *collect, term_t t) {
  bool saved_mode;
  term_t r;

  saved_mode = collect->bool_are_terms;
  collect->bool_are_terms = true;
  r = lit_collector_visit(collect, t);
  collect->bool_are_terms = saved_mode;

  return r;
}

/*
 * Process t (reduce Boolean terms to true/false)
 */
static term_t lit_collector_visit_formula(lit_collector_t *collect, term_t t) {
  bool saved_mode;
  term_t r;

  saved_mode = collect->bool_are_terms;
  collect->bool_are_terms = false;
  r = lit_collector_visit(collect, t);
  collect->bool_are_terms = saved_mode;

  return r;
}


/*
 * Processing t := (u == 0)
 * - if ELIM_ARITH_NEQ0 is enabled and t is false is the model,
 *   we replace (u /= 0) by either (u < 0) or (u > 0) depending
 *   on the sign of u in the model.
 */
static term_t lit_collector_visit_arith_eq_atom(lit_collector_t *collect, term_t t, term_t u) {
  term_t v, r;
  int sgn;

  v = lit_collector_visit(collect, u);
  if (lit_collector_option_enabled(collect, ELIM_ARITH_NEQ0)) {
    /*
     * Check whether (v == 0) is false
     */
    sgn = lit_collector_sign_in_model(collect, v);
    if (sgn < 0) {
      // atom is (v < 0), the result is false
      r = false_term;
      t = mk_arith_term_lt0(collect->manager, v);
    } else if (sgn  == 0) {
      // atom is (v == 0), the result is true
      r = true_term;
      if (v != u) {
	t = mk_arith_term_eq0(collect->manager, v);
      }
    } else {
      // atom is (v > 0)
      r = false_term;
      t = mk_arith_term_gt0(collect->manager, v);
    }

    // we know that t is true in the model
    lit_collector_add_literal(collect, t);

    return r;

  } else {
    // keep (u == 0) as a literal
    if (v != u) {
      t = mk_arith_term_eq0(collect->manager, v);
    }
    return register_atom(collect, t);
  }
}


/*
 * Arithmetic atom: (t1 == t2)
 * - if ELIM_ARITH_NEQ is enabled and (t1 != t2) in the model then we replace
 *   (not (t1 == t2)) by either (t1 < t2) or (t1 > t2)
 */
static term_t lit_collector_visit_arith_bineq(lit_collector_t *collect, term_t t, composite_term_t *eq) {
  term_t t1, t2, r;
  int cmp;

  assert(eq->arity == 2);
  t1 = lit_collector_visit(collect, eq->arg[0]);
  t2 = lit_collector_visit(collect, eq->arg[1]);

  if (lit_collector_option_enabled(collect, ELIM_ARITH_NEQ)) {
    /*
     * Check whether (t1 != t2) in the model
     */
    cmp = arith_cmp_in_model(collect, t1, t2);
    if (cmp < 0) {
      // atom (t1 < t2)
      r = false_term;
      t = mk_arith_lt(collect->manager, t1, t2);
    } else if (cmp == 0) {
      // atom (t1 == t2)
      r = true_term;
      if (t1 != eq->arg[0] || t2 != eq->arg[1]) {
	t = mk_arith_eq(collect->manager, t1, t2);
      }
    } else {
      // atom (t1 > t2)
      r = false_term;
      t = mk_arith_gt(collect->manager, t1, t2);
    }

    lit_collector_add_literal(collect, t);

    return r;

  } else {
    // keep the atom as (t1 == t2)
    if (t1 != eq->arg[0] || t2 != eq->arg[1]) {
      t = mk_arith_eq(collect->manager, t1, t2);
    }

    return register_atom(collect, t);
  }
}

// (/ t1 t2)
static term_t lit_collector_visit_arith_rdiv(lit_collector_t *collect, term_t t, composite_term_t *div) {
  term_t t1, t2;

  assert(div->arity == 2);
  t1 = lit_collector_visit(collect, div->arg[0]);
  t2 = lit_collector_visit(collect, div->arg[1]);
  if (t1 != div->arg[0] || t2 != div->arg[1]) {
    t = mk_arith_rdiv(collect->manager, t1, t2);
  }

  return t;
}

// (div t1 t2)
static term_t lit_collector_visit_arith_idiv(lit_collector_t *collect, term_t t, composite_term_t *div) {
  term_t t1, t2;

  assert(div->arity == 2);
  t1 = lit_collector_visit(collect, div->arg[0]);
  t2 = lit_collector_visit(collect, div->arg[1]);
  if (t1 != div->arg[0] || t2 != div->arg[1]) {
    t = mk_arith_idiv(collect->manager, t1, t2);
  }

  return t;
}

// (mod t1 t2)
static term_t lit_collector_visit_arith_mod(lit_collector_t *collect, term_t t, composite_term_t *mod) {
  term_t t1, t2;

  assert(mod->arity == 2);
  t1 = lit_collector_visit(collect, mod->arg[0]);
  t2 = lit_collector_visit(collect, mod->arg[1]);
  if (t1 != mod->arg[0] || t2 != mod->arg[1]) {
    t = mk_arith_mod(collect->manager, t1, t2);
  }

  return t;
}

// t is (divides k u)
static term_t lit_collector_visit_arith_divides_atom(lit_collector_t *collect, term_t t, composite_term_t *divides) {
  term_t k, u, v;

  assert(divides->arity == 2);

  k = divides->arg[0];
  u = divides->arg[1];

  assert(is_constant_term(collect->terms, k) && is_integer_term(collect->terms, k));
  
  v = lit_collector_visit(collect, u);
  if (v != u) {
    t = mk_arith_divides(collect->manager, k, v);
  }
  return register_atom(collect, t);
}


/*
 * (distinct t1 ... t_n)
 * We could do more:
 * 1) if (distinct t1 ... t_n) is false in the model, we could
 *    search for two terms t_i and t_j that are equal in the model then collect the
 *    atom (eq t_i t_j) instead of (not (distinct t1 ... t_n)).
 * 2) if (distinct t1 ... t_n) is true in the model and all t_i's are arithmetic
 *    terms, then we could sort them and generate the atoms:
 *    (< t_1 t_2) .... (< t_{n-1} t_n) (modulo permutation of the indices.
 */
static term_t lit_collector_visit_distinct(lit_collector_t *collect, term_t t, composite_term_t *distinct) {
  term_t *a;
  uint32_t i, n;

  n = distinct->arity;
  assert(n >= 3);

  a = alloc_istack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = lit_collector_visit(collect, distinct->arg[i]);
  }

  if (lit_collector_option_enabled(collect, ELIM_ARITH_DISTINCT) &&
      is_arithmetic_term(collect->terms, distinct->arg[0]) &&
      term_is_true_in_model(collect, t)) {
    /*
     * (distinct t1 ... t_n) is true in the model and t_1 ... t_n are arithmetic terms
     * convert to a conjunction of strict inequalities
     */
    lit_collector_sort_in_model(collect, n, a);
    for (i=0; i<n-1; i++) {
      t = mk_arith_lt(collect->manager, a[i], a[i+1]);
      lit_collector_add_literal(collect, t); // since t is true in the model
    }
    t = true_term;

  } else if (lit_collector_option_enabled(collect, ELIM_NOT_DISTINCT) &&
	     term_is_false_in_model(collect, t)) {
    /*
     * (distinct t1 ... t_n) is false in the model
     * search for two terms t_i and t_j that have same value in the model
     */
    lit_collector_sort_by_value(collect, n, a);
    for (i=0; i<n-1; i++) {
      if (equal_in_model(collect, a[i], a[i+1])) {
	t = mk_eq(collect->manager, a[i], a[i+1]);
	lit_collector_add_literal(collect, t); // t is true
	break;
      }
    }

    assert(i < n-1);

    t = false_term; // since (distinct ...) is false

  } else {
    /*
     * No special processing: keep distinct as an atom
     */
    if (inequal_arrays(a, distinct->arg, n)) {
      t = mk_distinct(collect->manager, n, a);
    }
    t = register_atom(collect, t);
  }

  free_istack_array(&collect->stack, a);

  return t;
}


/*
 * (eq t1 t2): special processing if t1 and t2 are Boolean and if one of them
 * is an uninterpreted term.
 */
static term_t lit_collector_visit_eq(lit_collector_t *collect, term_t t, composite_term_t *eq) {
  term_t u1, u2;
  term_t t1, t2;

  assert(eq->arity == 2);

  t1 = eq->arg[0];
  t2 = eq->arg[1];

  if (lit_collector_option_enabled(collect, KEEP_BOOL_EQ) &&
      is_boolean_term(collect->terms, t1)) {
    /*
     * Special processing: for Boolean equality
     * attempt to keep (eq t1 t2) as an atom.
     *
     * The default is to treat it as a disjunction:
     *   (or (and t1 t2) (and (not1 t1) (not t2)))
     */
    assert(is_boolean_term(collect->terms, t2));

    if (term_kind(collect->terms, t1) == UNINTERPRETED_TERM) {
      u1 = t1;
      // treat t2 as a term here
      u2 = lit_collector_visit_term(collect, t2);
      goto build_atom;
    }

    if (term_kind(collect->terms, t2) == UNINTERPRETED_TERM) {
      // treat t1 as a term
      u1 = lit_collector_visit_term(collect, t1);
      u2 = t2;
      goto build_atom;
    }
  }

  /*
   * Default processing:
   * - if bool_are_terms is true
   * - if KEEP_BOOL_EQ is disabled
   * - if t1 and t2 are not Boolean
   * - if neither t1 nor t2 is uninterpreted
   */
  u1 = lit_collector_visit_formula(collect, t1);
  u2 = lit_collector_visit_formula(collect, t2);

 build_atom:
  if (t1 != u1 || t2 != u2) {
    t = mk_eq(collect->manager, u1, u2);
  }

  return register_atom(collect, t);
}



// t is (u >= 0)  
static term_t lit_collector_visit_arith_ge_atom(lit_collector_t *collect, term_t t, term_t u) {
  term_t v;

  v = lit_collector_visit(collect, u);
  if (v != u) {
    t = mk_arith_term_geq0(collect->manager, v);
  }
  return register_atom(collect, t);
}

// t is (is_int u)  
static term_t lit_collector_visit_arith_is_int(lit_collector_t *collect, term_t t, term_t u) {
  term_t v;

  v = lit_collector_visit(collect, u);
  if (v != u) {
    t = mk_arith_is_int(collect->manager, v);
  }
  return register_atom(collect, t);
}

// t is (floor u)
static term_t lit_collector_visit_arith_floor(lit_collector_t *collect, term_t t, term_t u) {
  term_t v;

  v = lit_collector_visit(collect, u);
  if (v != u) {
    t = mk_arith_floor(collect->manager, v);
  }
  return t;
}

// t is (ceil u)
static term_t lit_collector_visit_arith_ceil(lit_collector_t *collect, term_t t, term_t u) {
  term_t v;

  v = lit_collector_visit(collect, u);
  if (v != u) {
    t = mk_arith_ceil(collect->manager, v);
  }
  return t;
}

// t is (abs u)  
static term_t lit_collector_visit_arith_abs(lit_collector_t *collect, term_t t, term_t u) {
  term_t v;

  v = lit_collector_visit(collect, u);
  if (v != u) {
    t = mk_arith_abs(collect->manager, v);
  }
  return t;
}


// (ite c t1 t2)
static term_t lit_collector_visit_ite(lit_collector_t *collect, term_t t, composite_term_t *ite) {
  term_t v, u;

  assert(ite->arity == 3);

  /*
   * We always process c as a formula so that it reduces to either true_term or false_term.
   */
  v = lit_collector_visit_formula(collect, ite->arg[0]);

  if (v == true_term) {
    u = ite->arg[1];  // t1
  } else {
    assert(v == false_term);
    u = ite->arg[2]; // t2
  }

  return lit_collector_visit(collect, u);
}

// (apply f t1 ... t_n)
static term_t lit_collector_visit_app(lit_collector_t *collect, term_t t, composite_term_t *app) {
  term_t *a;
  uint32_t i, n;

  n = app->arity;
  assert(n >= 2);

  // treat t1 ... t_n as terms
  a = alloc_istack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = lit_collector_visit_term(collect, app->arg[i]);
  }

  if (inequal_arrays(a, app->arg, n)) {
    t = mk_application(collect->manager, a[0], n-1, a+1);
  }
  free_istack_array(&collect->stack, a);

  if (is_boolean_term(collect->terms, t)) {
    t = register_atom(collect, t);
  }

  return t;
}

// (update f t1 ... t_n v)
static term_t lit_collector_visit_update(lit_collector_t *collect, term_t t, composite_term_t *update) {
  term_t *a;
  uint32_t i, n;

  n = update->arity;
  assert(n >= 3);

  a = alloc_istack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = lit_collector_visit_term(collect, update->arg[i]);
  }

  if (inequal_arrays(a, update->arg, n)) {
    t = mk_update(collect->manager, a[0], n-2, a+1, a[n-1]);
  }

  free_istack_array(&collect->stack, a);

  return t;
}

// (tuple t1 ... t_n)
static term_t lit_collector_visit_tuple(lit_collector_t *collect, term_t t, composite_term_t *tuple) {
  term_t *a;
  uint32_t i, n;

  n = tuple->arity;
  assert(n >= 1);

  a = alloc_istack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = lit_collector_visit_term(collect, tuple->arg[i]);
  }

  if (inequal_arrays(a, tuple->arg, n)) {
    t = mk_tuple(collect->manager, n, a);
  }

  free_istack_array(&collect->stack, a);

  return t;
}

// t is (or t1 ... t_n): treat it as a formula
static term_t lit_collector_visit_or_formula(lit_collector_t *collect, term_t t, composite_term_t *or) {
  term_t u;
  uint32_t i, n;

  n = or->arity;
  assert(n > 0);

  u = false_term; // prevent compilation warning

  if (term_is_true_in_model(collect, t)) {
    for (i=0; i<n; i++) {
      if (term_is_true_in_model(collect, or->arg[i])) break;
    }
    assert(i < n);
    u = lit_collector_visit_formula(collect, or->arg[i]);
    assert(u == true_term);

  } else {
    // (or t1 ... t_n) is false --> visit all subterms
    // they should all reduce to false_term
    for (i=0; i<n; i++) {
      u = lit_collector_visit_formula(collect, or->arg[i]);
      assert(u == false_term);
    }
  }

  return u;
}

// (xor t1 ... t_n): treat is as a formula
static term_t lit_collector_visit_xor_formula(lit_collector_t *collect, term_t t, composite_term_t *xor) {
  uint32_t i, n;
  term_t u;
  bool b;

  b = false;
  n = xor->arity;
  for (i=0; i<n; i++) {
    u = lit_collector_visit_formula(collect, xor->arg[i]);
    assert(u == false_term || u == true_term);
    b ^= (u == true_term);
  }
  return bool2term(b);
}

// (bv-array t1 ... tn)
static term_t lit_collector_visit_bvarray(lit_collector_t *collect, term_t t, composite_term_t *bv) {
  term_t *a;
  uint32_t i, n;

  n = bv->arity;
  assert(n >= 1);

  a = alloc_istack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    // maybe it would be better to call lit_collector_visit_term here?
    a[i] = lit_collector_visit(collect, bv->arg[i]);
  }

  t = mk_bvarray(collect->manager, n, a);

  free_istack_array(&collect->stack, a);

  return t;
}

// (bvdiv t1 t2)
static term_t lit_collector_visit_bvdiv(lit_collector_t *collect, term_t t, composite_term_t *bvdiv) {
  term_t t1, t2;

  assert(bvdiv->arity == 2);
  t1 = lit_collector_visit(collect, bvdiv->arg[0]);
  t2 = lit_collector_visit(collect, bvdiv->arg[1]);
  if (t1 != bvdiv->arg[0] || t2 != bvdiv->arg[1]) {
    t = mk_bvdiv(collect->manager, t1, t2);
  }

  return t;
}

// (bvrem t1 t2)
static term_t lit_collector_visit_bvrem(lit_collector_t *collect, term_t t, composite_term_t *bvrem) {
  term_t t1, t2;

  assert(bvrem->arity == 2);
  t1 = lit_collector_visit(collect, bvrem->arg[0]);
  t2 = lit_collector_visit(collect, bvrem->arg[1]);
  if (t1 != bvrem->arg[0] || t2 != bvrem->arg[1]) {
    t = mk_bvrem(collect->manager, t1, t2);
  }

  return t;
}

// (bvsdiv t1 t2)
static term_t lit_collector_visit_bvsdiv(lit_collector_t *collect, term_t t, composite_term_t *bvsdiv) {
  term_t t1, t2;

  assert(bvsdiv->arity == 2);
  t1 = lit_collector_visit(collect, bvsdiv->arg[0]);
  t2 = lit_collector_visit(collect, bvsdiv->arg[1]);
  if (t1 != bvsdiv->arg[0] || t2 != bvsdiv->arg[1]) {
    t = mk_bvsdiv(collect->manager, t1, t2);
  }

  return t;
}

// (bvsrem t1 t2)
static term_t lit_collector_visit_bvsrem(lit_collector_t *collect, term_t t, composite_term_t *bvsrem) {
  term_t t1, t2;

  assert(bvsrem->arity == 2);
  t1 = lit_collector_visit(collect, bvsrem->arg[0]);
  t2 = lit_collector_visit(collect, bvsrem->arg[1]);
  if (t1 != bvsrem->arg[0] || t2 != bvsrem->arg[1]) {
    t = mk_bvsrem(collect->manager, t1, t2);
  }

  return t;
}

// (bvsmod t1 t2)
static term_t lit_collector_visit_bvsmod(lit_collector_t *collect, term_t t, composite_term_t *bvsmod) {
  term_t t1, t2;

  assert(bvsmod->arity == 2);
  t1 = lit_collector_visit(collect, bvsmod->arg[0]);
  t2 = lit_collector_visit(collect, bvsmod->arg[1]);
  if (t1 != bvsmod->arg[0] || t2 != bvsmod->arg[1]) {
    t = mk_bvsmod(collect->manager, t1, t2);
  }

  return t;
}

// (bvshl t1 t2)
static term_t lit_collector_visit_bvshl(lit_collector_t *collect, term_t t, composite_term_t *bvshl) {
  term_t t1, t2;

  assert(bvshl->arity == 2);
  t1 = lit_collector_visit(collect, bvshl->arg[0]);
  t2 = lit_collector_visit(collect, bvshl->arg[1]);
  if (t1 != bvshl->arg[0] || t2 != bvshl->arg[1]) {
    t = mk_bvshl(collect->manager, t1, t2);
  }

  return t;
}

// (bvlshr t1 t2)
static term_t lit_collector_visit_bvlshr(lit_collector_t *collect, term_t t, composite_term_t *bvlshr) {
  term_t t1, t2;

  assert(bvlshr->arity == 2);
  t1 = lit_collector_visit(collect, bvlshr->arg[0]);
  t2 = lit_collector_visit(collect, bvlshr->arg[1]);
  if (t1 != bvlshr->arg[0] || t2 != bvlshr->arg[1]) {
    t = mk_bvlshr(collect->manager, t1, t2);
  }

  return t;
}

// (bvashr t1 t2)
static term_t lit_collector_visit_bvashr(lit_collector_t *collect, term_t t, composite_term_t *bvashr) {
  term_t t1, t2;

  assert(bvashr->arity == 2);
  t1 = lit_collector_visit(collect, bvashr->arg[0]);
  t2 = lit_collector_visit(collect, bvashr->arg[1]);
  if (t1 != bvashr->arg[0] || t2 != bvashr->arg[1]) {
    t = mk_bvashr(collect->manager, t1, t2);
  }

  return t;
}

// (bveq t1 t2)
static term_t lit_collector_visit_bveq(lit_collector_t *collect, term_t t, composite_term_t *bveq) {
  term_t t1, t2;

  assert(bveq->arity == 2);
  t1 = lit_collector_visit(collect, bveq->arg[0]);
  t2 = lit_collector_visit(collect, bveq->arg[1]);
  if (t1 != bveq->arg[0] || t2 != bveq->arg[1]) {
    t = mk_bveq(collect->manager, t1, t2);
  }

  return register_atom(collect, t);
}

// (bvge t1 t2)
static term_t lit_collector_visit_bvge(lit_collector_t *collect, term_t t, composite_term_t *bvge) {
  term_t t1, t2;

  assert(bvge->arity == 2);
  t1 = lit_collector_visit(collect, bvge->arg[0]);
  t2 = lit_collector_visit(collect, bvge->arg[1]);
  if (t1 != bvge->arg[0] || t2 != bvge->arg[1]) {
    t = mk_bvge(collect->manager, t1, t2);
  }

  return register_atom(collect, t);
}

// (bvsge t1 t2)
static term_t lit_collector_visit_bvsge(lit_collector_t *collect, term_t t, composite_term_t *bvsge) {
  term_t t1, t2;

  assert(bvsge->arity == 2);
  t1 = lit_collector_visit(collect, bvsge->arg[0]);
  t2 = lit_collector_visit(collect, bvsge->arg[1]);
  if (t1 != bvsge->arg[0] || t2 != bvsge->arg[1]) {
    t = mk_bvsge(collect->manager, t1, t2);
  }

  return register_atom(collect, t);
}

// (select i u)
static term_t lit_collector_visit_select(lit_collector_t *collect, term_t t, select_term_t *select) {
  term_t u, v;
  uint32_t i;

  /*
   * select may become an invalid pointer if new terms are created
   * so we extract u and i before the recursive call to visit.
   */
  u = select->arg;
  i = select->idx;

  v = lit_collector_visit(collect, u);
  if (v != u) {
    t = mk_select(collect->manager, i, v);
  }

  if (is_boolean_term(collect->terms, t)) {
    t = register_atom(collect, t);
  }

  return t;
}

// (bit i u)
static term_t lit_collector_visit_bit(lit_collector_t *collect, term_t t, select_term_t *bit) {
  term_t u, v;
  uint32_t i;

  /*
   * bit may become an invalid pointer if new terms are created
   * so we extract u and i before the recursive call to visit.
   */
  u = bit->arg;
  i = bit->idx;

  v = lit_collector_visit(collect, u);
  if (v != u) {
    t = mk_bitextract(collect->manager, v, i);
  }

  return register_atom(collect, t);
}

// power product
static term_t lit_collector_visit_pprod(lit_collector_t *collect, term_t t, pprod_t *p) {
  term_t *a;
  uint32_t i, n;

  n = p->len;
  a = alloc_istack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = lit_collector_visit(collect, p->prod[i].var);
  }

  if (inequal_array_pprod(a, p)) {
    t = mk_pprod(collect->manager, p, n, a);
  }

  free_istack_array(&collect->stack, a);

  return t;
}

// polynomial (rational coefficients)
static term_t lit_collector_visit_poly(lit_collector_t *collect, term_t t, polynomial_t *p) {
  term_t *a;
  uint32_t i, n;

  n = p->nterms;
  a = alloc_istack_array(&collect->stack, n);

  // skip the constant term if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[i] = const_idx;
    i ++;
  }

  // rest of p
  while (i < n) {
    a[i] = lit_collector_visit(collect, p->mono[i].var);
    i ++;
  }

  if (inequal_array_poly(a, p)) {
    t = mk_arith_poly(collect->manager, p, n, a);
  }

  free_istack_array(&collect->stack, a);

  return t;
}

// bitvector polynomial (coefficients are 64bit or less)
static term_t lit_collector_visit_bvpoly64(lit_collector_t *collect, term_t t, bvpoly64_t *p) {
  term_t *a;
  uint32_t i, n;

  n = p->nterms;
  a = alloc_istack_array(&collect->stack, n);

  // skip the constant term if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[i] = const_idx;
    i ++;
  }

  // rest of p
  while (i < n) {
    a[i] = lit_collector_visit(collect, p->mono[i].var);
    i ++;
  }

  if (inequal_array_bvpoly64(a, p)) {
    t = mk_bvarith64_poly(collect->manager, p, n, a);
  }

  free_istack_array(&collect->stack, a);

  return t;
}

// bitvector polynomials (coefficients more than 64bits)
static term_t lit_collector_visit_bvpoly(lit_collector_t *collect, term_t t, bvpoly_t *p) {
  term_t *a;
  uint32_t i, n;

  n = p->nterms;
  a = alloc_istack_array(&collect->stack, n);

  // skip the constant term if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[i] = const_idx;
    i ++;
  }

  // rest of p
  while (i < n) {
    a[i] = lit_collector_visit(collect, p->mono[i].var);
    i ++;
  }

  if (inequal_array_bvpoly(a, p)) {
    t = mk_bvarith_poly(collect->manager, p, n, a);
  }

  free_istack_array(&collect->stack, a);

  return t;
}


/*
 * Process term t:
 * - if t is in the cache (already visited) return the corresponding term
 * - otherwise explore t and return its simplified version
 * - the atoms found while exploring t are added to collect->lit_set
 */
static term_t lit_collector_visit(lit_collector_t *collect, term_t t) {
  term_table_t *terms;
  uint32_t polarity;
  term_t u;

  polarity = polarity_of(t);
  t = unsigned_term(t);

  u = lit_collector_find_cached_term(collect, t);
  if (u == NULL_TERM) {
    terms = collect->terms;
    switch (term_kind(terms, t)) {
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
      u = t;
      break;

    case VARIABLE:
      longjmp(collect->env, MDL_EVAL_FREEVAR_IN_TERM);
      break;

    case UNINTERPRETED_TERM:
      if (is_boolean_term(terms, t)) {
	u = register_atom(collect, t);
      } else {
	u = t;
      }
      break;

    case ARITH_EQ_ATOM:
      u = lit_collector_visit_arith_eq_atom(collect, t, arith_eq_arg(terms, t));
      break;

    case ARITH_GE_ATOM:
      u = lit_collector_visit_arith_ge_atom(collect, t, arith_ge_arg(terms, t));
      break;

    case ARITH_IS_INT_ATOM:
      u = lit_collector_visit_arith_is_int(collect, t, arith_is_int_arg(terms, t));
      break;

    case ARITH_FLOOR:
      u = lit_collector_visit_arith_floor(collect, t, arith_floor_arg(terms, t));
      break;

    case ARITH_CEIL:
      u = lit_collector_visit_arith_ceil(collect, t, arith_ceil_arg(terms, t));
      break;

    case ARITH_ABS:
      u = lit_collector_visit_arith_abs(collect, t, arith_abs_arg(terms, t));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
      u = lit_collector_visit_ite(collect, t, ite_term_desc(terms, t));
      break;

    case APP_TERM:
      u = lit_collector_visit_app(collect, t, app_term_desc(terms, t));
      break;

    case UPDATE_TERM:
      u = lit_collector_visit_update(collect, t, update_term_desc(terms, t));
      break;

    case TUPLE_TERM:
      u = lit_collector_visit_tuple(collect, t, tuple_term_desc(terms, t));
      break;

    case EQ_TERM:
      u = lit_collector_visit_eq(collect, t, eq_term_desc(terms, t));
      break;

    case DISTINCT_TERM:
      u = lit_collector_visit_distinct(collect, t, distinct_term_desc(terms, t));
      break;

    case FORALL_TERM:
      longjmp(collect->env, MDL_EVAL_QUANTIFIER);
      break;

    case LAMBDA_TERM:
      longjmp(collect->env, MDL_EVAL_LAMBDA);
      break;

      //ARITH_ROOT_ATOM should get its very longjmp 

    case OR_TERM:
      u = lit_collector_visit_or_formula(collect, t, or_term_desc(terms, t));
      break;

    case XOR_TERM:
      u = lit_collector_visit_xor_formula(collect, t, xor_term_desc(terms, t));
      break;

    case ARITH_BINEQ_ATOM:
      u = lit_collector_visit_arith_bineq(collect, t, arith_bineq_atom_desc(terms, t));
      break;

    case ARITH_RDIV:
      u = lit_collector_visit_arith_rdiv(collect, t, arith_rdiv_term_desc(terms, t));
      break;
      
    case ARITH_IDIV:
      u = lit_collector_visit_arith_idiv(collect, t, arith_idiv_term_desc(terms, t));
      break;
      
    case ARITH_MOD:
      u = lit_collector_visit_arith_mod(collect, t, arith_mod_term_desc(terms, t));
      break;

    case ARITH_DIVIDES_ATOM:
      u = lit_collector_visit_arith_divides_atom(collect, t, arith_divides_atom_desc(terms, t));
      break;

    case BV_ARRAY:
      u = lit_collector_visit_bvarray(collect, t, bvarray_term_desc(terms, t));
      break;

    case BV_DIV:
      u = lit_collector_visit_bvdiv(collect, t, bvdiv_term_desc(terms, t));
      break;

    case BV_REM:
      u = lit_collector_visit_bvrem(collect, t, bvrem_term_desc(terms, t));
      break;

    case BV_SDIV:
      u = lit_collector_visit_bvsdiv(collect, t, bvsdiv_term_desc(terms, t));
      break;

    case BV_SREM:
      u = lit_collector_visit_bvsrem(collect, t, bvsrem_term_desc(terms, t));
      break;

    case BV_SMOD:
      u = lit_collector_visit_bvsmod(collect, t, bvsmod_term_desc(terms, t));
      break;

    case BV_SHL:
      u = lit_collector_visit_bvshl(collect, t, bvshl_term_desc(terms, t));
      break;

    case BV_LSHR:
      u = lit_collector_visit_bvlshr(collect, t, bvlshr_term_desc(terms, t));
      break;

    case BV_ASHR:
      u = lit_collector_visit_bvashr(collect, t, bvashr_term_desc(terms, t));
      break;

    case BV_EQ_ATOM:
      u = lit_collector_visit_bveq(collect, t, bveq_atom_desc(terms, t));
      break;

    case BV_GE_ATOM:
      u = lit_collector_visit_bvge(collect, t, bvge_atom_desc(terms, t));
      break;

    case BV_SGE_ATOM:
      u = lit_collector_visit_bvsge(collect, t, bvsge_atom_desc(terms, t));
      break;

    case SELECT_TERM:
      u = lit_collector_visit_select(collect, t, select_term_desc(terms, t));
      break;

    case BIT_TERM:
      u = lit_collector_visit_bit(collect, t, bit_term_desc(terms, t));
      break;

    case POWER_PRODUCT:
      u = lit_collector_visit_pprod(collect, t, pprod_term_desc(terms, t));
      break;

    case ARITH_POLY:
      u = lit_collector_visit_poly(collect, t, poly_term_desc(terms, t));
      break;

    case BV64_POLY:
      u = lit_collector_visit_bvpoly64(collect, t, bvpoly64_term_desc(terms, t));
      break;

    case BV_POLY:
      u = lit_collector_visit_bvpoly(collect, t, bvpoly_term_desc(terms, t));
      break;

    case UNUSED_TERM:
    case RESERVED_TERM:
    default:
      //iam: fprintf(stderr, "lit_collector_visit %d\n", term_kind(terms, t));
      assert(false);
      longjmp(collect->env, MDL_EVAL_INTERNAL_ERROR);
      break;
    }
    lit_collector_cache_result(collect, t, u);
  }

  return u ^ polarity;
}


/*
 * Top-level call: process term t:
 * - return an atomic term u equal to t  modulo the literals in collect->lit_set
 * - add literals of t to collect->lit_set
 *
 * - return a negative error code if something goes wrong.
 */
term_t lit_collector_process(lit_collector_t *collect, term_t t) {
  term_t u;

  u = setjmp(collect->env);
  if (u == 0) {
    u = lit_collector_visit(collect, t);
  } else {
    assert(u < 0); // error code after longjmp
    reset_istack(&collect->stack);
  }

  return u;
}


/*
 * Store the literals of collect->lit_set into vector v
 */
void lit_collector_get_literals(lit_collector_t *collect, ivector_t *v) {
  int_hset_t *set;
  term_t t;
  uint32_t i, n;

  set = &collect->lit_set;
  int_hset_close(set);
  n = set->nelems;
  for (i=0; i<n; i++) {
    t = set->data[i];
    assert(is_true_in_model(collect, t));
    ivector_push(v, t);
  }
}


/*
 * GET IMPLICANT FOR ASSERTIONS GIVEN A MODEL
 */

/*
 * Given a model mdl and a set of formulas a[0 ... n-1] satisfied by mdl,
 * compute an implicant for a[0] /\ a[1] /\ ... /\ a[n-2].
 * - mngr = term manager with mngr->terms == mdl->terms
 * - all terms in a must be Boolean and all of them must be true in mdl
 * - if there's a error, the function returns a negative code
 *   and leaves v unchanged
 * - otherwise, the function returns 0 and adds the implicant literals to vector
 *   v  (v is not reset).
 *
 * - options = bit mask to enable/disable the optional processing.
 */
int32_t get_implicant(model_t *mdl, term_manager_t *mngr, uint32_t options,
		      uint32_t n, const term_t *a, ivector_t *v) {
  lit_collector_t collect;
  int32_t u;
  uint32_t i;

  init_lit_collector(&collect, mdl, mngr);
  lit_collector_set_option(&collect, options);
  for (i=0; i<n; i++) {
    u = lit_collector_process(&collect, a[i]);
    if (u < 0) goto done; // exception in process
    if (u == false_term) {
      // formula a[i] is false in the model
      u = MDL_EVAL_FORMULA_FALSE;
      goto done;
    }
    assert(u == true_term);
  }

  // Extract the implicants. They are stored in collect.lit_set
  lit_collector_get_literals(&collect, v);

  // Return code = 0 (no error);
  u = 0;

 done:
  delete_lit_collector(&collect);
  return u;
}

