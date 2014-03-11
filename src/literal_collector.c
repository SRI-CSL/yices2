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

#include "literal_collector.h"

/*
 * Initialization: prepare collector for model mdl
 * - collect->env is not touched.
 */
void init_lit_collector(lit_collector_t *collect, model_t *mdl) {
  collect->terms = mdl->terms;
  collect->model = mdl;
  init_evaluator(&collect->eval, mdl);
  init_term_manager(&collect->manager, mdl->terms);
  init_int_hmap(&collect->cache, 0);
  init_int_hset(&collect->lit_set, 0);
  init_istack(&collect->stack);
}


/*
 * Delete everything
 */
void delete_lit_collector(lit_collector_t *collect) {
  delete_evaluator(&collect->eval);
  delete_term_manager(&collect->manager);
  delete_int_hmap(&collect->cache);
  delete_int_hset(&collect->lit_set);
  delete_istack(&collect->stack);
}


/*
 * Reset: empty the lit_set and the cache
 */
void reset_lit_collector(lit_collector_t *collect) {
  int_hmap_reset(&collect->cache);
  int_hset_reset(&collect->lit_set);
  reset_istack(&collect->stack);
}


/*
 * Get the term mapped to t in collect->cache
 * - return NULL_TERM if t is not in the cache
 */
static term_t lit_collector_find_cached_term(lit_collector_t *collect, term_t t) {
  int_hmap_pair_t *r;
  term_t u;

  assert(good_term(collect->terms, t));

  u = NULL_TERM;
  r = int_hmap_find(&collect->cache, t);
  if (r != NULL) {
    u = r->val;
    assert(good_term(collect->terms, u));
  }

  return u;
}


/*
 * Store the mapping t --> u in the cache
 */
static void lit_collector_cache_result(lit_collector_t *collect, term_t t, term_t u) {
  int_hmap_pair_t *r;

  assert(good_term(collect->terms, t) && good_term(collect->terms, u));

  r = int_hmap_get(&collect->cache, t);
  assert(r != NULL && r->val == -1);
  r->val = u;
}


/*
 * Check whether t is true in the model
 * - t must be a Boolean term
 */
static bool term_is_true_in_model(lit_collector_t *collect, term_t t) {
  value_t v;

  assert(is_boolean_term(collect->terms, t));

  v = eval_in_model(&collect->eval, t);
  if (v < 0) {
    // error in the evaluation
    longjmp(collect->env, LIT_COLLECT_EVAL_FAILED);
    // We could return false here?
  }

  return is_true(&collect->model->vtbl, v);
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
 * Add t to the set of literals
 * - t must be a true in the model
 */
static void lit_collector_add_literal(lit_collector_t *collect, term_t t) {
  assert(is_true_in_model(collect, t));
  (void) int_hset_add(&collect->lit_set, t);
}


/*
 * Found an atom t:
 * - add either t or not(t) to the set of literals
 * - return true_term or false_term (i.e., value of t in the model)
 */
static term_t register_atom(lit_collector_t *collect, term_t t) {
  term_t u;

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
 * Process a term t: collect literals of t and return an atomic term
 * equal to t modulo the literals.
 */
static term_t lit_collector_visit(lit_collector_t *collect, term_t t);

/*
 * Processing of non-atomic terms
 */

// (t == 0)
static term_t lit_collector_visit_eq_atom(lit_collector_t *collect, term_t t) {
  return NULL_TERM;
}

// (t >= 0)
static term_t lit_collector_visit_ge_atom(lit_collector_t *collect, term_t t) {
  return NULL_TERM;
}

// (ite c t1 t2)
static term_t lit_collector_visit_ite(lit_collector_t *collect, composite_term_t *ite) {
  return NULL_TERM;
}

// (apply f t1 ... t_n)
static term_t lit_collector_visit_app(lit_collector_t *collect, composite_term_t *app) {
  return NULL_TERM;
}

// (update f t1 ... t_n v)
static term_t lit_collector_visit_update(lit_collector_t *collect, composite_term_t *update) {
  return NULL_TERM;
}

// (tuple t1 ... t_n)
static term_t lit_collector_visit_tuple(lit_collector_t *collect, composite_term_t *tuple) {
  return NULL_TERM;
}

// (eq t1 t2)
static term_t lit_collector_visit_eq(lit_collector_t *collect, composite_term_t *eq) {
  return NULL_TERM;
}

// (distinct t1 ... t_n)
static term_t lit_collector_visit_distinct(lit_collector_t *collect, composite_term_t *distinct) {
  return NULL_TERM;
}

// t is (or t1 ... t_n)
static term_t lit_collector_visit_or(lit_collector_t *collect, term_t t, composite_term_t *or) {
  return NULL_TERM;
}

// (xor t1 ... t_n)
static term_t lit_collector_visit_xor(lit_collector_t *collect, composite_term_t *xor) {
  return NULL_TERM;
}

// (arith-eq t1 t2)
static term_t lit_collector_visit_arith_bineq(lit_collector_t *collect, composite_term_t *eq) {
  return NULL_TERM;
}

// (bv-array t1 ... tn)
static term_t lit_collector_visit_bvarray(lit_collector_t *collect, composite_term_t *bv) {
  return NULL_TERM;
}

// (bvdiv t1 t2)
static term_t lit_collector_visit_bvdiv(lit_collector_t *collect, composite_term_t *bvdiv) {
  return NULL_TERM;
}

// (bvrem t1 t2)
static term_t lit_collector_visit_bvrem(lit_collector_t *collect, composite_term_t *bvrem) {
  return NULL_TERM;
}

// (bvsdiv t1 t2)
static term_t lit_collector_visit_bvsdiv(lit_collector_t *collect, composite_term_t *bvsdiv) {
  return NULL_TERM;
}

// (bvsrem t1 t2)
static term_t lit_collector_visit_bvsrem(lit_collector_t *collect, composite_term_t *bvsrem) {
  return NULL_TERM;
}

// (bvsmod t1 t2)
static term_t lit_collector_visit_bvsmod(lit_collector_t *collect, composite_term_t *bvsmod) {
  return NULL_TERM;
}

// (bvshl t1 t2)
static term_t lit_collector_visit_bvshl(lit_collector_t *collect, composite_term_t *bvshl) {
  return NULL_TERM;
}

// (bvlshr t1 t2)
static term_t lit_collector_visit_bvlshr(lit_collector_t *collect, composite_term_t *bvlshr) {
  return NULL_TERM;
}

// (bvashr t1 t2)
static term_t lit_collector_visit_bvashr(lit_collector_t *collect, composite_term_t *bvashr) {
  return NULL_TERM;
}

// (bveq t1 t2)
static term_t lit_collector_visit_bveq(lit_collector_t *collect, composite_term_t *bveq) {
  return NULL_TERM;
}

// (bvge t1 t2)
static term_t lit_collector_visit_bvge(lit_collector_t *collect, composite_term_t *bvge) {
  return NULL_TERM;
}

// (bvsge t1 t2)
static term_t lit_collector_visit_bvsge(lit_collector_t *collect, composite_term_t *bvsge) {
  return NULL_TERM;
}

// (select i t)
static term_t lit_collector_visit_select(lit_collector_t *collect, select_term_t *select) {
  return NULL_TERM;
}

// (bit i u)
static term_t lit_collector_visit_bit(lit_collector_t *collect, select_term_t *bit) {
  return NULL_TERM;
}

// power product
static term_t lit_collector_visit_pprod(lit_collector_t *collect, pprod_t *p) {
  return NULL_TERM;
}

// polynomial (rational coefficients)
static term_t lit_collector_visit_poly(lit_collector_t *collect, polynomial_t *p) {
  return NULL_TERM;
}

// bitvector polynomial (coefficients are 64bit or less)
static term_t lit_collector_visit_bvpoly64(lit_collector_t *collect, bvpoly64_t *p) {
  return NULL_TERM;
}

// bitvector polynomials (coefficients more than 64bits)
static term_t lit_collector_visit_bvpoly(lit_collector_t *collect, bvpoly_t *p) {
  return NULL_TERM;
}


/*
 * Process term t:
 * - if t is in the cache (already visited) return the corresponding term
 * - otherwise explore t and return its simplified version
 * - also add atoms found while exploring t
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
      longjmp(collect->env, LIT_COLLECT_FREEVAR_IN_TERM);
      break;

    case UNINTERPRETED_TERM:
      if (is_boolean_term(terms, t)) {
	u = register_atom(collect, t);
      } else {
	u = t;
      }
      break;

    case ARITH_EQ_ATOM:
      u = lit_collector_visit_eq_atom(collect, arith_eq_arg(terms, t));
      break;

    case ARITH_GE_ATOM:
      u = lit_collector_visit_ge_atom(collect, arith_ge_arg(terms, t));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
      u = lit_collector_visit_ite(collect, ite_term_desc(terms, t));
      break;

    case APP_TERM:
      u = lit_collector_visit_app(collect, app_term_desc(terms, t));
      break;

    case UPDATE_TERM:
      u = lit_collector_visit_update(collect, update_term_desc(terms, t));
      break;

    case TUPLE_TERM:
      u = lit_collector_visit_tuple(collect, tuple_term_desc(terms, t));
      break;

    case EQ_TERM:
      u = lit_collector_visit_eq(collect, eq_term_desc(terms, t));
      break;

    case DISTINCT_TERM:
      u = lit_collector_visit_distinct(collect, distinct_term_desc(terms, t));
      break;

    case FORALL_TERM:
      longjmp(collect->env, LIT_COLLECT_QUANTIFIER);
      break;

    case LAMBDA_TERM:
      longjmp(collect->env, LIT_COLLECT_LAMBDA);
      break;

    case OR_TERM:
      u = lit_collector_visit_or(collect, t, or_term_desc(terms, t));
      break;

    case XOR_TERM:
      u = lit_collector_visit_xor(collect, xor_term_desc(terms, t));
      break;

    case ARITH_BINEQ_ATOM:
      u = lit_collector_visit_arith_bineq(collect, arith_bineq_atom_desc(terms, t));
      break;

    case BV_ARRAY:
      u = lit_collector_visit_bvarray(collect, bvarray_term_desc(terms, t));
      break;

    case BV_DIV:
      u = lit_collector_visit_bvdiv(collect, bvdiv_term_desc(terms, t));
      break;

    case BV_REM:
      u = lit_collector_visit_bvrem(collect, bvrem_term_desc(terms, t));
      break;

    case BV_SDIV:
      u = lit_collector_visit_bvsdiv(collect, bvsdiv_term_desc(terms, t));
      break;

    case BV_SREM:
      u = lit_collector_visit_bvsrem(collect, bvsrem_term_desc(terms, t));
      break;

    case BV_SMOD:
      u = lit_collector_visit_bvsmod(collect, bvsmod_term_desc(terms, t));
      break;

    case BV_SHL:
      u = lit_collector_visit_bvshl(collect, bvshl_term_desc(terms, t));
      break;

    case BV_LSHR:
      u = lit_collector_visit_bvlshr(collect, bvlshr_term_desc(terms, t));
      break;

    case BV_ASHR:
      u = lit_collector_visit_bvashr(collect, bvashr_term_desc(terms, t));
      break;

    case BV_EQ_ATOM:
      u = lit_collector_visit_bveq(collect, bveq_atom_desc(terms, t));
      break;

    case BV_GE_ATOM:
      u = lit_collector_visit_bvge(collect, bvge_atom_desc(terms, t));
      break;

    case BV_SGE_ATOM:
      u = lit_collector_visit_bvsge(collect, bvge_atom_desc(terms, t));
      break;

    case SELECT_TERM:
      u = lit_collector_visit_select(collect, select_term_desc(terms, t));
      break;

    case BIT_TERM:
      u = lit_collector_visit_bit(collect, bit_term_desc(terms, t));
      break;

    case POWER_PRODUCT:
      u = lit_collector_visit_pprod(collect, pprod_term_desc(terms, t));
      break;

    case ARITH_POLY:
      u = lit_collector_visit_poly(collect, poly_term_desc(terms, t));
      break;

    case BV64_POLY:
      u = lit_collector_visit_bvpoly64(collect, bvpoly64_term_desc(terms, t));
      break;

    case BV_POLY:
      u = lit_collector_visit_bvpoly(collect, bvpoly_term_desc(terms, t));
      break;

    case UNUSED_TERM:
    case RESERVED_TERM:
    default:
      assert(false);
      longjmp(collect->env, LIT_COLLECT_INTERNAL_ERROR);
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
