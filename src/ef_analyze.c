/*
 * Processing for formulas for EF-solving
 */

#include <assert.h>

#include "ef_analyze.h"



/*
 * EF CLAUSES
 */

void init_ef_clause(ef_clause_t *cl) {
  init_ivector(&cl->evars, 10);
  init_ivector(&cl->uvars, 10);
  init_ivector(&cl->assumptions, 10);
  init_ivector(&cl->guarantees, 10);
}

void reset_ef_clause(ef_clause_t *cl) {
  ivector_reset(&cl->evars);
  ivector_reset(&cl->uvars);
  ivector_reset(&cl->assumptions);
  ivector_reset(&cl->guarantees);
}

void delete_ef_clause(ef_clause_t *cl) {
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
 * ANALYZER
 */

/*
 * Initialize an analyzer structure
 */
void init_ef_analyzer(ef_analyzer_t *ef, term_manager_t *mngr) {
  ef->terms = term_manager_get_terms(mngr);
  ef->manager = mngr;
  init_int_queue(&ef->queue, 0);
  init_int_hset(&ef->cache, 128);
  init_ivector(&ef->flat, 64);
  init_ivector(&ef->disjuncts, 64);
  init_ivector(&ef->evars, 32);
  init_ivector(&ef->uvars, 32);
}


/*
 * Reset queue and cache
 */
void reset_ef_analyzer(ef_analyzer_t *ef) {
  int_queue_reset(&ef->queue);
  int_hset_reset(&ef->cache);
  ivector_reset(&ef->flat);
  ivector_reset(&ef->disjuncts);
  ivector_reset(&ef->evars);
  ivector_reset(&ef->uvars);
}


/*
 * Delete
 */
void delete_ef_analyzer(ef_analyzer_t *ef) {
  delete_int_queue(&ef->queue);
  delete_int_hset(&ef->cache);
  delete_ivector(&ef->flat);
  delete_ivector(&ef->disjuncts);
  delete_ivector(&ef->evars);
  delete_ivector(&ef->uvars);
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
	u = d->arg[1]; // A
	v = d->arg[2]; // B
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
      if (is_neg_term(t)) {
	/*
	 * t is (not (or a[0] ... a[n-1]))
	 * it flattens to (and (not a[0]) ... (not a[n-1]))
	 */
	d = or_term_desc(terms, t);
	n = d->arity;
	for (i=0; i<n; i++) {
	  ef_push_term(ef, opposite_term(d->arg[i]));
	}
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
void ef_add_assertions(ef_analyzer_t *ef, uint32_t n, term_t *a, bool f_ite, bool f_iff, ivector_t *v) {
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
	u = d->arg[1]; // A
	v = d->arg[2]; // B
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
void ef_flatten_to_disjuncts(ef_analyzer_t *ef, term_t t, bool f_ite, bool f_iff, ivector_t *v) {
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
 * Process term t:
 * - check whether t is quantifier free
 * - collect its free variables in uvar and its uninterpreted
 *   terms in evar
 */
bool ef_get_vars(ef_analyzer_t *ef, term_t t, ivector_t *uvar, ivector_t *evar) {
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
bool all_atomic_vars(ef_analyzer_t *ef, ivector_t *v) {
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
bool all_basic_vars(ef_analyzer_t *ef, ivector_t *v) {
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
uint32_t remove_uninterpreted_functions(ef_analyzer_t *ef, ivector_t *v) {
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
 * - t is written to (or A_1(y) .... A_k(y) G_1(x, y) ... G_t(x, y))
 *   where x = uninterpreted constants of t (existentials)
 *     and y = free variables of t (universal variables)
 * - A_i = any term that contains only the y variables
 *   G_j = any other term
 * - the set of universal variables are collected in cl->uvars
 *   the set of existential variables are collected in cl->evars
 *   the A_i's are stored in cl->assumptions
 *   the G_j's are stored in cl->guarantees
 */
ef_code_t ef_decompose(ef_analyzer_t *ef, term_t t, ef_clause_t *cl) {
  ivector_t *v;
  uint32_t i, n;
  ef_code_t c, code;

  reset_ef_clause(cl);
  v = &ef->disjuncts;
  ef_flatten_to_disjuncts(ef, t, true, true, v);
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


