/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Processing for formulas for EF-solving
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <assert.h>

#include "terms/term_utils.h"
#include "solvers/exists_forall/ef_analyze.h"
#include "terms/term_sets.h"
#include "terms/elim_subst.h"

#include "yices.h"


/*
 * EF CLAUSES
 */
static void init_ef_clause(ef_clause_t *cl) {
  init_ivector(&cl->evars, 10);
  init_ivector(&cl->uvars, 10);
  init_ivector(&cl->assumptions, 10);
  init_ivector(&cl->guarantees, 10);
}

static void reset_ef_clause(ef_clause_t *cl) {
  ivector_reset(&cl->evars);
  ivector_reset(&cl->uvars);
  ivector_reset(&cl->assumptions);
  ivector_reset(&cl->guarantees);
}

static void delete_ef_clause(ef_clause_t *cl) {
  delete_ivector(&cl->evars);
  delete_ivector(&cl->uvars);
  delete_ivector(&cl->assumptions);
  delete_ivector(&cl->guarantees);
}



/*
 * Add t to the assumptions or guarantees vector
 */
static void ef_clause_add_assumption(ef_clause_t *cl, term_t t) {
  ivector_push(&cl->assumptions, t);
}

static void ef_clause_add_guarantee(ef_clause_t *cl, term_t t) {
  ivector_push(&cl->guarantees, t);
}

/*
 * Add a[0 ... n-1] to the exitential or universal variables
 */
static void ef_clause_add_evars(ef_clause_t *cl, term_t *a, uint32_t n) {
  if (n > 0) {
    ivector_add(&cl->evars, a, n);
    ivector_remove_duplicates(&cl->evars);
  }
}

static void ef_clause_add_uvars(ef_clause_t *cl, term_t *a, uint32_t n) {
  if (n > 0) {
    ivector_add(&cl->uvars, a, n);
    ivector_remove_duplicates(&cl->uvars);
  }
}


/*
 * Print a clause
 */
void print_ef_clause(FILE *f, ef_clause_t *cl) {
  fprintf(f, "EF Clause: evars\n");
  yices_pp_term_array(f, cl->evars.size, cl->evars.data, 120, UINT32_MAX, 0, 1);
  fprintf(f, "\nEF Clause: uvars\n");
  yices_pp_term_array(f, cl->uvars.size, cl->uvars.data, 120, UINT32_MAX, 0, 1);
  fprintf(f, "\nEF Clause: assumptions\n");
  yices_pp_term_array(f, cl->assumptions.size, cl->assumptions.data, 120, UINT32_MAX, 0, 0);
  fprintf(f, "\nEF Clause: guarantees\n");
  yices_pp_term_array(f, cl->guarantees.size, cl->guarantees.data, 120, UINT32_MAX, 0, 0);
  fprintf(f, "---\n");
}



/*
 * ANALYZER
 */

/*
 * Initialize an analyzer structure
 */
void init_ef_analyzer(ef_analyzer_t *ef, term_manager_t *mngr) {
  ef->terms = term_manager_get_terms(mngr);
  ef->manager = mngr;
  init_term_subst(&ef->subst, mngr, 0, NULL, NULL); // empty substitution
  init_int_queue(&ef->queue, 0);
  init_int_hset(&ef->cache, 128);
  init_ivector(&ef->flat, 64);
  init_ivector(&ef->disjuncts, 64);
  init_ivector(&ef->evars, 32);
  init_ivector(&ef->uvars, 32);
  init_ivector(&ef->aux, 10);
}


/*
 * Reset queue and cache
 */
void reset_ef_analyzer(ef_analyzer_t *ef) {
  reset_term_subst(&ef->subst);
  int_queue_reset(&ef->queue);
  int_hset_reset(&ef->cache);
  ivector_reset(&ef->flat);
  ivector_reset(&ef->disjuncts);
  ivector_reset(&ef->evars);
  ivector_reset(&ef->uvars);
  ivector_reset(&ef->aux);
}


/*
 * Delete
 */
void delete_ef_analyzer(ef_analyzer_t *ef) {
  delete_term_subst(&ef->subst);
  delete_int_queue(&ef->queue);
  delete_int_hset(&ef->cache);
  delete_ivector(&ef->flat);
  delete_ivector(&ef->disjuncts);
  delete_ivector(&ef->evars);
  delete_ivector(&ef->uvars);
  delete_ivector(&ef->aux);
}



/*
 * FLATTENING OPERATIONS
 */

/*
 * Check whether t is in the cache.
 * If not, add t to the cache and to the end of the queue
 */
static void ef_push_term(ef_analyzer_t *ef, term_t t) {
  if (int_hset_add(&ef->cache, t)) {
    int_queue_push(&ef->queue, t);
  }
}


/*
 * Check whether we should apply distributivity to (or a[0] .... a[n-1)
 * - heuristic: return true if exactly one of a[i] is a conjunct
 */
static bool ef_distribute_is_cheap(ef_analyzer_t *ef, composite_term_t *d) {
  term_table_t *terms;
  uint32_t i, n;
  bool result;
  term_t t;

  terms = ef->terms;
  result = false;
  n = d->arity;
  for (i=0; i<n; i++) {
    t = d->arg[i];
    if (is_neg_term(t) && term_kind(terms, t) == OR_TERM) {
      // t is not (or ...) i.e., a conjunct
      result = !result;
      if (!result) break;  // second conjunct
    }
  }

  return result;
}

/*
 * Apply distributivity and flatten
 * - this function rewrites
 *     (or a[0] ... a[n-2] (and b[0] ... b[m-1]))
 *   to (and (or a[0] ... a[n-2] b[0])
 *            ...
 *           (or a[0] ... a[n-2] b[m-1]))
 *   then push all terms
 *      (or a[0] ... a[n-1] b[j]) to the queue
 *
 * - the rewriting is applied to the first a[j] that's a conjunct.
 */
static void ef_flatten_distribute(ef_analyzer_t *ef, composite_term_t *d) {
  term_table_t *terms;
  composite_term_t *b;
  ivector_t *v;
  uint32_t i, j, k, n, m;
  term_t t;

  terms = ef->terms;

  j = 0; // Stop GCC warning

  /*
   * Find the first term among a[0 ... n-1] that's of the form (not (or ...))
   * - store that term's descriptor in b
   * - store its index in j
   */
  b = NULL;
  n = d->arity;
  for (i=0; i<n; i++) {
    t = d->arg[i];
    if (is_neg_term(t) && term_kind(terms, t) == OR_TERM && b == NULL) {
      b = or_term_desc(terms, t);
      j = i;
    }
  }

  /*
   * a[j] is (not (or b[0] ... b[m-1])) == not b
   * d->arg is (or a[0] ... a[n-1])
   */
  assert(b != NULL);

  v = &ef->aux;
  m = b->arity;
  for (k=0; k<m; k++) {
    /*
     * IMPORTANT: we make a full copy of d->arg into v
     * at every iteration of this loop. This is required because
     * mk_or modifies v->data.
     */
    ivector_reset(v);
    ivector_push(v, opposite_term(b->arg[k]));   // this is not b[k]
    for (i=0; i<n; i++) {
      if (i != j) {
	ivector_push(v, d->arg[i]); // a[i] for i/=j
      }
    }
    t = mk_or(ef->manager, v->size, v->data);  // t is (or b[i] a[0] ...)
    ef_push_term(ef, t);
  }
}


/*
 * Process all terms in ef->queue: flatten conjuncts and universal quantifiers
 * - store the result in resu
 * - f_ite: if true, also flatten any Boolean if-then-else
 *   f_iff: if true, also flatten any iff term
 */
static void ef_flatten_forall_conjuncts(ef_analyzer_t *ef, bool f_ite, bool f_iff, ivector_t *resu) {
  term_table_t *terms;
  int_queue_t *queue;
  composite_term_t *d;
  term_t t, u, v;
  uint32_t i, n;

  queue = &ef->queue;
  terms = ef->terms;

  while (! int_queue_is_empty(queue)) {
    t = int_queue_pop(queue);

    switch (term_kind(terms, t)) {
    case ITE_TERM:
    case ITE_SPECIAL:
      d = ite_term_desc(terms, t);
      assert(d->arity == 3);
      if (f_ite && is_boolean_term(terms, d->arg[1])) {
	assert(is_boolean_term(terms, d->arg[2]));
	/*
	 * If t is (ite C A B)
	 *    u := (C => A)
	 *    v := (not C => B)
	 * Otherwise, t is (not (ite C A B))
	 *    u := (C => not A)
	 *    v := (not C => not B)
	 */
	u = d->arg[1];  // A
	v = d->arg[2];  // B
	if (is_neg_term(t)) {
	  u = opposite_term(u);
	  v = opposite_term(v);
	}
	u = mk_implies(ef->manager, d->arg[0], u); // (C => u)
	v = mk_implies(ef->manager, opposite_term(d->arg[0]), v); // (not C) => v
	ef_push_term(ef, u);
	ef_push_term(ef, v);
	continue;
      }
      break;

    case EQ_TERM:
      d = eq_term_desc(terms, t);
      assert(d->arity == 2);
      if (f_iff && is_boolean_term(terms, d->arg[0])) {
	assert(is_boolean_term(terms, d->arg[1]));
	/*
	 * t is either (iff A B) or (not (iff A B)):
	 */
	u = d->arg[0]; // A
	v = d->arg[1]; // B
	if (is_neg_term(t)) {
	  u = opposite_term(u);
	}
	// flatten to (u => v) and (v => u)
	t = mk_implies(ef->manager, u, v); // (u => v)
	u = mk_implies(ef->manager, v, u); // (v => u);
	ef_push_term(ef, t);
	ef_push_term(ef, u);
	continue;
      }
      break;

    case OR_TERM:
      d = or_term_desc(terms, t);
      if (is_neg_term(t)) {
	/*
	 * t is (not (or a[0] ... a[n-1]))
	 * it flattens to (and (not a[0]) ... (not a[n-1]))
	 */
	n = d->arity;
	for (i=0; i<n; i++) {
	  ef_push_term(ef, opposite_term(d->arg[i]));
	}
	continue;
      } else if (ef_distribute_is_cheap(ef, d)) {
	ef_flatten_distribute(ef, d);
	continue;
      }
      break;

    case FORALL_TERM:
      if (is_pos_term(t)) {
	d = forall_term_desc(terms, t);
	n = d->arity;
	assert(n >= 2);
	/*
	 * t is (FORALL x_0 ... x_k : body)
	 * body is the last argument in the term descriptor
	 */
	ef_push_term(ef, d->arg[n-1]);
	continue;
      }
      break;

    default:
      break;
    }

    // t was not flattened: add it to resu
    ivector_push(resu, t);
  }

  // clean up the cache
  assert(int_queue_is_empty(queue));
  int_hset_reset(&ef->cache);
}


/*
 * Add assertions and flatten them to conjuncts
 * - n = number of assertions
 * - a = array of n assertions
 *
 * - any formula a[i] of the form (and A B ...) is flattened
 *   also any formula a[i] of the form (forall y : C) is replaced by C
 *   this is done recursively, and the result is stored in vector v
 *
 * - optional processing:
 *   if f_ite is true, flatten (ite c a b) to (c => a) and (not c => b)
 *   if f_iff is true, flatten (iff a b)   to (a => b) and (b => a)
 *
 * Note: this does not do type checking. If any term in a is not Boolean,
 * it is kept as is in the ef->flat vector.
 */
static void ef_add_assertions(ef_analyzer_t *ef, uint32_t n, term_t *a, bool f_ite, bool f_iff, ivector_t *v) {
  uint32_t i;

  assert(int_queue_is_empty(&ef->queue) && int_hset_is_empty(&ef->cache));

  ivector_reset(v);
  for (i=0; i<n; i++) {
    ef_push_term(ef, a[i]);
  }
  ef_flatten_forall_conjuncts(ef, f_ite, f_iff, v);
}



/*
 * FLATTENING OF DISJUNCTIONS
 */

/*
 * Process all terms in ef->queue: flatten disjuncts
 * - store the result in resu
 * - f_ite: if true, also flatten Boolean if-then-else
 *   f_iff: if true, also flatten iff
 */
static void ef_build_disjuncts(ef_analyzer_t *ef, bool f_ite, bool f_iff, ivector_t *resu) {
  term_table_t *terms;
  int_queue_t *queue;
  composite_term_t *d;
  term_t t, u, v;
  uint32_t i, n;

  queue = &ef->queue;
  terms = ef->terms;

  while (! int_queue_is_empty(queue)) {
    t = int_queue_pop(queue);

    switch (term_kind(terms, t)) {
    case ITE_TERM:
    case ITE_SPECIAL:
      d = ite_term_desc(terms, t);
      assert(d->arity == 3);
      if (f_ite && is_boolean_term(terms, d->arg[1])) {
	assert(is_boolean_term(terms, d->arg[2]));
	/*
	 * If t is (ite C A B)
	 *    u := (C AND A)
	 *    v := (not C AND B)
	 * Otherwise, t is (not (ite C A B))
	 *    u := (C AND not A)
	 *    v := (not C AND not B)
	 */
	u = d->arg[1];  // A
	v = d->arg[2];  // B
	if (is_neg_term(t)) {
	  u = opposite_term(u); // NOT A
	  v = opposite_term(v); // NOT B
	}
	u = mk_binary_and(ef->manager, d->arg[0], u); // (C AND u)
	v = mk_binary_and(ef->manager, opposite_term(d->arg[0]), v); // (not C) AND v
	ef_push_term(ef, u);
	ef_push_term(ef, v);
	continue;
      }
      break;

    case EQ_TERM:
      d = eq_term_desc(terms, t);
      assert(d->arity == 2);
      if (f_iff && is_boolean_term(terms, d->arg[0])) {
	assert(is_boolean_term(terms, d->arg[1]));
	/*
	 * t is either (iff A B) or (not (iff A B)):
	 */
	u = d->arg[0]; // A
	v = d->arg[1]; // B
	if (is_neg_term(t)) {
	  u = opposite_term(u);
	}
	// flatten to (u AND v) or ((not u) AND (not v))
	t = mk_binary_and(ef->manager, u, v); // (u AND v)
	u = mk_binary_and(ef->manager, opposite_term(u), opposite_term(v)); // (not u AND not v);
	ef_push_term(ef, t);
	ef_push_term(ef, u);
	continue;
      }
      break;

    case OR_TERM:
      if (is_pos_term(t)) {
	/*
	 * t is (or a[0] ... a[n-1])
	 */
	d = or_term_desc(terms, t);
	n = d->arity;
	for (i=0; i<n; i++) {
	  ef_push_term(ef, d->arg[i]);
	}
	continue;
      }
      break;

    default:
      break;
    }

    ivector_push(resu, t);
  }

  // clean up the cache
  assert(int_queue_is_empty(queue));
  int_hset_reset(&ef->cache);
}

/*
 * Convert t to a set of disjuncts
 * - the result is stored in vector v
 * - optional processing:
 *   if f_ite is true (ite c a b) is rewritten to (c and a) or ((not c) and b)
 *   if f_iff is true (iff a b)   is rewritten to (a and b) or ((not a) and (not b))
 */
static void ef_flatten_to_disjuncts(ef_analyzer_t *ef, term_t t, bool f_ite, bool f_iff, ivector_t *v) {
  assert(int_queue_is_empty(&ef->queue) && int_hset_is_empty(&ef->cache));

  ivector_reset(v);
  ef_push_term(ef, t);
  ef_build_disjuncts(ef, f_ite, f_iff, v);
}



/*
 * VARIABLE EXTRACTION
 */

/*
 * Add t to the queue if it's not already visited (i.e., not in the cache)
 * For the purpose of ef analyzer, x and (not x) are the same, so we
 * always remove the polarity bit of t here.
 */
static void ef_push_unsigned_term(ef_analyzer_t *ef, term_t t) {
  t = unsigned_term(t); // remove polarity bit
  if (int_hset_add(&ef->cache, t)) {
    int_queue_push(&ef->queue, t);
  }
}


/*
 * Explore a composite term: add all its children to the queue
 */
static void ef_analyze_composite(ef_analyzer_t *ef, composite_term_t *d) {
  uint32_t i, n;

  n = d->arity;
  for (i=0; i<n; i++) {
    ef_push_unsigned_term(ef, d->arg[i]);
  }
}


/*
 * Power product
 */
static void ef_analyze_power_product(ef_analyzer_t *ef, pprod_t *p) {
  uint32_t i, n;

  n = p->len;
  for (i=0; i<n; i++) {
    ef_push_unsigned_term(ef, p->prod[i].var);
  }
}


/*
 * Polynomials: skipt the constant part if any
 */
static void ef_analyze_poly(ef_analyzer_t *ef, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) i++;
  while (i < n) {
    ef_push_unsigned_term(ef, p->mono[i].var);
    i++;
  }
}

static void ef_analyze_bvpoly64(ef_analyzer_t *ef, bvpoly64_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) i++;
  while (i < n) {
    ef_push_unsigned_term(ef, p->mono[i].var);
    i++;
  }
}

static void ef_analyze_bvpoly(ef_analyzer_t *ef, bvpoly_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) i++;
  while (i < n) {
    ef_push_unsigned_term(ef, p->mono[i].var);
    i++;
  }
}


/*
 * Collect variables of t and check that it's quantifier free
 * - return true if t is quantifier free
 * - return false otherwise
 * - collect the variables of t in vector uvar (universal vars)
 * - collect the uninterpreted constants of t in vector evar (existential vars)
 */
static bool ef_get_vars(ef_analyzer_t *ef, term_t t, ivector_t *uvar, ivector_t *evar) {
  term_table_t *terms;
  int_queue_t *queue;

  assert(int_queue_is_empty(&ef->queue) && int_hset_is_empty(&ef->cache));

  terms = ef->terms;
  queue = &ef->queue;

  ivector_reset(uvar);
  ivector_reset(evar);

  ef_push_unsigned_term(ef, t);

  while (! int_queue_is_empty(queue)) {
    t = int_queue_pop(queue);
    assert(is_pos_term(t));

    switch (term_kind(terms, t)) {
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
      break;

    case VARIABLE:
      ivector_push(uvar, t);
      break;

    case UNINTERPRETED_TERM:
      ivector_push(evar, t);
      break;

    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
      ef_push_unsigned_term(ef, arith_atom_arg(terms, t));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case APP_TERM:
    case UPDATE_TERM:
    case TUPLE_TERM:
    case EQ_TERM:
    case DISTINCT_TERM:
    case OR_TERM:
    case XOR_TERM:
    case ARITH_BINEQ_ATOM:
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
      ef_analyze_composite(ef, composite_term_desc(terms, t));
      break;

    case FORALL_TERM:
    case LAMBDA_TERM:
      goto bad_ef_term;

    case SELECT_TERM:
      ef_push_unsigned_term(ef, select_term_arg(terms, t));
      break;

    case BIT_TERM:
      ef_push_unsigned_term(ef, bit_term_arg(terms, t));
      break;

    case POWER_PRODUCT:
      ef_analyze_power_product(ef, pprod_term_desc(terms, t));
      break;

    case ARITH_POLY:
      ef_analyze_poly(ef, poly_term_desc(terms, t));
      break;

    case BV64_POLY:
      ef_analyze_bvpoly64(ef, bvpoly64_term_desc(terms, t));
      break;

    case BV_POLY:
      ef_analyze_bvpoly(ef, bvpoly_term_desc(terms, t));
      break;

    default:
      assert(false);
      break;
    }
  }

  int_hset_reset(&ef->cache);
  return true;

 bad_ef_term:
  int_queue_reset(&ef->queue);
  int_hset_reset(&ef->cache);
  return false;
}


/*
 * VALIDATION OF VARIABLE LISTS
 */

/*
 * Check that all variables of v have atomic types
 */
static bool all_atomic_vars(ef_analyzer_t *ef, ivector_t *v) {
  term_table_t *terms;
  uint32_t i, n;
  type_t tau;

  terms = ef->terms;

  n = v->size;
  for (i=0; i<n; i++) {
    tau = term_type(terms, v->data[i]);
    if (! is_atomic_type(terms->types, tau)) {
      return false;
    }
  }

  return true;
}


/*
 * Check whether tau is a basic type in the given type table
 */
static bool is_basic_type(type_table_t *types, type_t tau) {
  return is_atomic_type(types, tau) ||
    (is_function_type(types, tau) && type_depth(types, tau) == 1);
}

/*
 * Check that all (existential variables of v) have either an atomic type
 * or a type [-> tau_1 ... tau_n sigma] where the tau_i's and sigma are atomic.
 */
static bool all_basic_vars(ef_analyzer_t *ef, ivector_t *v) {
  term_table_t *terms;
  type_table_t *types;
  uint32_t i, n;
  type_t tau;

  terms = ef->terms;
  types = terms->types;

  n = v->size;
  for (i=0; i<n; i++) {
    tau = term_type(terms, v->data[i]);
    if (! is_basic_type(types, tau)) {
      return false;
    }
  }

  return true;
}


/*
 * Remove uninterpreted function symbols from v
 * - this is intended to be used for v that satisfies all_basic_vars
 * - return the number of terms removed
 */
static uint32_t remove_uninterpreted_functions(ef_analyzer_t *ef, ivector_t *v) {
  term_table_t *terms;
  term_t x;
  uint32_t i, j, n;

  terms = ef->terms;

  j = 0;
  n = v->size;
  for (i=0; i<n; i++) {
    x = v->data[i];
    if (! is_function_term(terms, x)) {
      // keep x
      v->data[j] = x;
      j ++;
    }
  }

  ivector_shrink(v, j);

  return n - j;
}



/*
 * Get the variables of t and check for errors
 * - remove all uninterpreted functions from the evar (if any)
 */
static ef_code_t ef_get_vars_and_check(ef_analyzer_t *ef, term_t t, ivector_t *uvar, ivector_t *evar) {
  ef_code_t c;

  c = EF_NO_ERROR;
  if (!ef_get_vars(ef, t, uvar, evar)) {
    // t is not quantifier free
    c = EF_NESTED_QUANTIFIER;
  } else if (!all_atomic_vars(ef, uvar)) {
    c = EF_HIGH_ORDER_UVAR;
  } else if (!all_basic_vars(ef, evar)) {
    c = EF_HIGH_ORDER_EVAR;
  } else if (remove_uninterpreted_functions(ef, evar) > 0)  {
    c = EF_UNINTERPRETED_FUN;
  }

  return c;
}



/*
 * Decompose term t into an Exist/Forall clause
 * - t is rewritten to (or A_1(y) .... A_k(y) G_1(x, y) ... G_t(x, y))
 *   where x = uninterpreted constants of t (existentials)
 *     and y = free variables of t (universal variables)
 * - f_ite, f_iff: optional flattening flags
 * - A_i = any term that contains only the y variables
 *   G_j = any other term
 * - the set of universal variables are collected in cl->uvars
 *   the set of existential variables are collected in cl->evars
 *   the A_i's are stored in cl->assumptions
 *   the G_j's are stored in cl->guarantees
 */
static ef_code_t ef_decompose(ef_analyzer_t *ef, term_t t, ef_clause_t *cl, bool f_ite, bool f_iff) {
  ivector_t *v;
  uint32_t i, n;
  ef_code_t c, code;

  reset_ef_clause(cl);
  v = &ef->disjuncts;
  ef_flatten_to_disjuncts(ef, t, f_ite, f_iff, v);
  code = EF_NO_ERROR; // default

  n = v->size;
  for (i=0; i<n; i++) {
    /*
     * Process disjunct v->data[i] and check for errors
     */
    t = v->data[i];
    c = ef_get_vars_and_check(ef, t, &ef->uvars, &ef->evars);
    if (c > EF_UNINTERPRETED_FUN) return c; // fatal error
    if (c == EF_UNINTERPRETED_FUN) {
      code = c;
    }

    /*
     * Add t to the clause
     */
    ef_clause_add_evars(cl, ef->evars.data, ef->evars.size);
    ef_clause_add_uvars(cl, ef->uvars.data, ef->uvars.size);
    if (ef->uvars.size > 0 && ef->evars.size == 0) {
      // t contains universal variables and no existential variables
      ef_clause_add_assumption(cl, t);
    } else {
      ef_clause_add_guarantee(cl, t);
    }
  }

  return code;
}


/*
 * CONVERSION TO GROUND TERMS
 */

/*
 * The assumptions and guarantees may contain free variables (i.e.,
 * instances of universal variables). Since the context can't deal
 * with free variables in terms, we convert variables to uninterpreted
 * terms (of the same type and name).
 *
 * This is done by building a substitution that maps variables to thier
 * clones.
 */

/*
 * Return the clone of variable x:
 * - if x is already in ef->subst's domain, return what's mapped to x
 * - otherwise, create a clone for x and add the map [x --> clone]
 *   to ef_subst.
 */
static term_t ef_clone_uvar(ef_analyzer_t *ef, term_t x) {
  term_t clone;

  assert(term_kind(ef->terms, x) == VARIABLE);

  clone = term_subst_var_mapping(&ef->subst, x);
  if (clone < 0) {
    clone = variable_to_unint(ef->terms, x);
    extend_term_subst1(&ef->subst, x, clone, false);
  }

  assert(term_kind(ef->terms, clone) == UNINTERPRETED_TERM);

  return clone;
}


/*
 * Replace all elements of v by their clones
 * - all elements must be variabale
 */
static void ef_clone_uvar_array(ef_analyzer_t *ef, term_t *v, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    v[i] = ef_clone_uvar(ef, v[i]);
  }
}


/*
 * Convert term t that may contain universal variable into a ground
 * term (by replacing all universal variables with their clones).
 */
static term_t ef_make_ground(ef_analyzer_t *ef, term_t t) {
  term_t g;

  g = apply_term_subst(&ef->subst, t);
  // the substitution should not fail
  assert(good_term(ef->terms, g));

  return g;
}


/*
 * Apply make_ground to all elements of array a
 */
static void ef_make_array_ground(ef_analyzer_t *ef, term_t *t, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    t[i] = ef_make_ground(ef, t[i]);
  }
}


/*
 * Compute the or of formulas in v
 */
static term_t ef_make_or(ef_analyzer_t *ef, ivector_t *v) {
  uint32_t n;
  term_t r;

  n = v->size;
  if (n == 0) {
    r = false_term;
  } else if (n == 1) {
    r = v->data[0];
  } else {
    r = mk_or(ef->manager, n, v->data);
  }

  return r;
}


/*
 * Simplify a clause: attempt to remove universal variables by substitution
 * - search for literals of the form (/= y t) in the guarantees and assumptions
 * - then apply a substitution: i.e., convert (or (/= y t) ... (P y) ...))
 *   into (or ... (P t) ...)
 */
static void ef_simplify_clause(ef_analyzer_t *ef, ef_clause_t *c) {
  int_hset_t uvars;
  elim_subst_t elim;
  uint32_t i, j, n;
  term_t x, t, u;

  init_term_set(&uvars, c->uvars.size, c->uvars.data);
  init_elim_subst(&elim, ef->manager, &uvars);

  // try to convert the guarantees and assumptions into a substitution
  n = c->guarantees.size;
  for (i=0; i<n; i++) {
    t = opposite_term(c->guarantees.data[i]);
    (void) elim_subst_try_map(&elim, t, false);
  }
  n = c->assumptions.size;
  for (i=0; i<n; i++) {
    t = opposite_term(c->assumptions.data[i]);
    (void) elim_subst_try_map(&elim, t, false);
  }

  elim_subst_remove_cycles(&elim);

  // remove the universal variables that can be eliminated
  n = c->uvars.size;
  j = 0;
  for (i=0; i<n; i++) {
    x = c->uvars.data[i];
    t = elim_subst_get_map(&elim, x);
    // TEMPORARY: print the substitution
    if (t >= 0) {
#if 0
      printf("Elimination:\n %s --> ", yices_get_term_name(x));
      yices_pp_term(stdout, t, 100, 20, 12);
#endif
    } else {
      // x is kept in uvars
      c->uvars.data[j] = x;
      j ++;
    }
  }
  ivector_shrink(&c->uvars, j);


  if (j < n) {
    /*
     * Some universal variables can be eliminated.
     * Apply the substitution to all the terms of c.
     *
     * The substitution may introduce existential variables in the
     * assumptions (so they should be moved to the guarantees vector).
     * Crude approach for now: if an assumption is modified, we move it
     * to the guarantees vector.
     */
    n = c->guarantees.size;
    j = 0;
    for (i=0; i<n; i++) {
      t = c->guarantees.data[i];
      u = elim_subst_apply(&elim, t);
      if (u != false_term) {
	c->guarantees.data[j] = u;
	j ++;
      }
    }
    ivector_shrink(&c->guarantees, j);

    n = c->assumptions.size;
    j = 0;
    for (i=0; i<n; i++) {
      t = c->assumptions.data[i];
      u = elim_subst_apply(&elim, t);
      if (t == u) {
	c->assumptions.data[j] = t;
	j ++;
      } else if (u != false_term) {
	ef_clause_add_guarantee(c, u);
      }
    }
    ivector_shrink(&c->assumptions, j);
  }


  delete_elim_subst(&elim);
  delete_term_set(&uvars);
}


/*
 * Add clause c to an ef_prob descriptor
 * - t = term that decomposed into c
 *
 * Processing:
 * 1) if c has  no universal  variables, then  term t  is added  as a
 *    condition to the problem, and all evars are added to prob.
 * 2) otherwise, c contains assumptions   A_1(y) ... A_n(y)
 *    and guarantees G_1(x, y) ... G_k(x, y)
 *    We build A := not (OR A_1(y) ... A_n(y))
 *             G := (OR G_1(x, y) ... G_k(x, y))
 *    then convert all instances of universal variables to uninterpreted terms.
 *    So both A and G are ground terms.
 *    Then we add the universal constrains (forall y: A => G) to prob.
 */
static void ef_add_clause(ef_analyzer_t *ef, ef_prob_t *prob, term_t t, ef_clause_t *c) {
  term_t a, g;

  if (c->uvars.size == 0) {
    // no universal variables
    ef_prob_add_condition(prob, t);
    ef_prob_add_evars(prob, c->evars.data, c->evars.size);

  } else {
    // convert all uvars to clones and make ground
    ef_clone_uvar_array(ef, c->uvars.data, c->uvars.size);
    ef_make_array_ground(ef, c->assumptions.data, c->assumptions.size);
    ef_make_array_ground(ef, c->guarantees.data, c->guarantees.size);

    // simplify the clause: attempt to eliminate some universal variables.
#if 0
    printf("\nINITIAL CLAUSE\n\n");
    print_ef_clause(stdout, c);
#endif
    ef_simplify_clause(ef, c);
#if 0
    printf("\nAFTER SIMPLIFICATION\n\n");
    print_ef_clause(stdout, c);
#endif

    // build the assumption: not (or c->assumptions)
    a = opposite_term(ef_make_or(ef, &c->assumptions));

    // guarantee = or c->guarantees
    g = ef_make_or(ef, &c->guarantees);

    ef_prob_add_constraint(prob, c->evars.data, c->evars.size,
			   c->uvars.data, c->uvars.size, a, g);
  }
}


/*
 * FULL PROCESSING
 */
/*
 * Full processing:
 * - build problem descriptor from a set of assertions
 *   n = number of assertions
 *   a[0 ... n-1] = the assertions
 *   f_ite: flag to enable flattening of if-then-else
 *   f_iff: flag to enable flattening of iff
 * - result code: same as ef_decompose
 * - if code is either EF_NO_ERROR or EF_UNINTERPRETED_FUN then prob is
 *   filled in with the problem
 * - otherwise, prob is partially filled in.
 */
ef_code_t ef_analyze(ef_analyzer_t *ef, ef_prob_t *prob, uint32_t n, term_t *a, bool f_ite, bool f_iff) {
  ef_clause_t clause;
  ivector_t *v;
  uint32_t i;
  term_t t;
  ef_code_t c, return_code;

  assert(ef_prob_is_empty(prob) && prob->terms == ef->terms);

  return_code = EF_NO_ERROR;

  init_ef_clause(&clause);

  v = &ef->flat;
  ef_add_assertions(ef, n, a, f_ite, f_iff, v);

  n = v->size;
  for (i=0; i<n; i++) {
    t = v->data[i];
    c = ef_decompose(ef, t, &clause, f_ite, f_iff);
    switch (c) {
    case EF_UNINTERPRETED_FUN:
      return_code = c; // fall through intended
    case EF_NO_ERROR:
      ef_add_clause(ef, prob, t, &clause);
      break;
    default: // error
      return_code = c;
      goto done;
    }
  }

 done:
  delete_ef_clause(&clause);
  return return_code;
}
