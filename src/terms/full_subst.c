/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * FULL SUBSTITUTION
 */

#include "terms/term_substitution.h"
#include "terms/full_subst.h"

/*
 * Marks for cycle detection
 */
enum {
  MARK_WHITE,
  MARK_GREY,
  MARK_BLACK,
};


/*
 * Initialization:
 * - mngr = term_manager to use
 */
void init_full_subst(full_subst_t *subst, term_manager_t *mngr) {
  subst->mngr = mngr;
  subst->terms = term_manager_get_terms(mngr);
  init_int_hmap(&subst->map, 0);
  init_mark_vector(&subst->mark, 0, (uint8_t) MARK_WHITE);
  subst->remove_cycles = false;
  init_int_hmap(&subst->cache, 0);
  init_istack(&subst->stack);
  init_ivector(&subst->aux, 0);
}


/*
 * Delete the whole thing
 */
void delete_full_subst(full_subst_t *subst) {
  delete_int_hmap(&subst->map);
  delete_mark_vector(&subst->mark);
  delete_int_hmap(&subst->cache);
  delete_istack(&subst->stack);
  delete_ivector(&subst->aux);
}



#ifndef NDEBUG
/*
 * Simple check on mapping: [x --> t]
 * - x must be uninterpreted
 * - t's type must be a subtype of x's type
 * (we don't check that t is ground)
 */
static bool good_map_types(full_subst_t *subst, term_t x, term_t t) {
  term_table_t *terms;

  terms = subst->terms;

  assert(good_term(terms, x) && good_term(terms, t));
  return is_pos_term(x) &&
    term_kind(terms, x) == UNINTERPRETED_TERM &&
    is_subtype(terms->types, term_type(terms, t), term_type(terms, x));
}
#endif



/*
 * ACCESS TO THE MAP
 */

/*
 * Check what's mapped to x
 * - x must be an uninterpreted term in subst->terms
 * - return  NULL_TERM if nothing is mapped to x
 */
term_t full_subst_get_map(full_subst_t *subst, term_t x) {
  int_hmap_pair_t *r;
  term_t v;

  assert(term_kind(subst->terms, x) == UNINTERPRETED_TERM);
  v = NULL_TERM;
  r = int_hmap_find(&subst->map, x);
  if (r != NULL) {
    v = r->val;
  }

  return v;
}

/*
 * Add mapping [x --> t] to subst
 * - x and t must be valid terms in subst->terms
 * - x must be an uninterpreted term
 *   t must be a ground term
 * - t's type must be a subtype of x's type
 * - x must not be mapped to anything yet
 */
void full_subst_add_map(full_subst_t *subst, term_t x, term_t t) {
  int_hmap_pair_t *r;

  assert(good_map_types(subst, x, t));

  r = int_hmap_get(&subst->map, x);
  assert(r->val < 0);
  r->val = t;
}


/*
 * Remove the mapping for x
 * - x must be mapped to something
 */
static void full_subst_remove_map(full_subst_t *subst, term_t x) {
  int_hmap_pair_t *r;

  assert(term_kind(subst->terms, x) == UNINTERPRETED_TERM);
  r = int_hmap_find(&subst->map, x);
  assert(r != NULL && r->val >= 0);
  r->val = NULL_TERM;
}


/*
 * CYCLE DETECTION
 */

/*
 * We use a depth-first search: visit(t) returns true if t is on
 * a substitution cycle
 * - mark of t:
 *   WHITE means t not visited yet
 *   GREY  means t has been visited but not all its descendants
 *   BLACK means t and all its descendants have been explored
 *
 * NOTE: we attach the mark to term indices (so t and not(t) have the
 * same mark)
 *
 * - if subst->remove_cycles is false, then the function just detect cycles.
 * - if subst->remove_cylces is true, then it removes cycles by
 *   removing [x := t] from the map, for the first x that causes a cycle.
 *
 */

static bool fsubst_visit(full_subst_t *subst, term_t t);

static bool fsubst_visit_composite(full_subst_t *subst, composite_term_t *c) {
  uint32_t i, n;

  n = c->arity;
  for (i=0; i<n; i++) {
    if (fsubst_visit(subst, c->arg[i])) {
      return true;
    }
  }

  return false;
}

static bool fsubst_visit_pprod(full_subst_t *subst, pprod_t *p) {
  uint32_t i, n;

  n = p->len;
  for (i=0; i<n; i++) {
    if (fsubst_visit(subst, p->prod[i].var)) {
      return true;
    }
  }

  return false;
}

static bool fsubst_visit_arith_poly(full_subst_t *subst, polynomial_t *p) {
  monomial_t *m;
  uint32_t i, n;

  m = p->mono;
  n = p->nterms;
  assert(n > 0);
  // skip constant marker
  if (m[0].var == const_idx) {
    m++;
    n--;
  }

  for (i=0; i<n; i++) {
    if (fsubst_visit(subst, m[i].var)) {
      return true;
    }
  }

  return false;
}

static bool fsubst_visit_bv_poly(full_subst_t *subst, bvpoly_t *p) {
  bvmono_t *m;
  uint32_t i, n;

  m = p->mono;
  n = p->nterms;
  assert(n > 0);
  // skip constant marker
  if (m[0].var == const_idx) {
    m++;
    n--;
  }

  for (i=0; i<n; i++) {
    if (fsubst_visit(subst, m[i].var)) {
      return true;
    }
  }

  return false;
}

static bool fsubst_visit_bv64_poly(full_subst_t *subst, bvpoly64_t *p) {
  bvmono64_t *m;
  uint32_t i, n;

  m = p->mono;
  n = p->nterms;
  assert(n > 0);
  // skip constant marker
  if (m[0].var == const_idx) {
    m++;
    n--;
  }

  for (i=0; i<n; i++) {
    if (fsubst_visit(subst, m[i].var)) {
      return true;
    }
  }

  return false;
}

// mark i grey and explore its descendants
static bool fsubst_explore(full_subst_t *subst, int32_t i) {
  term_table_t *terms;
  bool result;
  term_t s;

  terms = subst->terms;

  assert(good_term_idx(terms, i) && mark_vector_get_mark(&subst->mark, i) == MARK_WHITE);

  mark_vector_add_mark(&subst->mark, i, MARK_GREY);
  result = false; // default = no cycle

  switch (kind_for_idx(terms, i)) {
  case CONSTANT_TERM:
  case ARITH_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
    break;

  case UNINTERPRETED_TERM:
    // follow the map
    s = full_subst_get_map(subst, pos_term(i));
    if (s != NULL_TERM) {
      result = fsubst_visit(subst, s);
      if (result && subst->remove_cycles) {
	// remove the mapping pos_term(i) := s to break the cycle
	full_subst_remove_map(subst, pos_term(i));
	result = false;
      }
    }
    break;

  case VARIABLE: // subst maps vars to themselves
    break;

  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
    result = fsubst_visit(subst, integer_value_for_idx(terms, i));
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
  case APP_TERM:
  case UPDATE_TERM:
  case TUPLE_TERM:
  case EQ_TERM:
  case DISTINCT_TERM:
  case FORALL_TERM:
  case LAMBDA_TERM:
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
    result = fsubst_visit_composite(subst, composite_for_idx(terms, i));
    break;

  case SELECT_TERM:
  case BIT_TERM:
    result = fsubst_visit(subst, select_for_idx(terms, i)->arg);
    break;

  case POWER_PRODUCT:
    result = fsubst_visit_pprod(subst, pprod_for_idx(terms, i));
    break;

  case ARITH_POLY:
    result = fsubst_visit_arith_poly(subst, polynomial_for_idx(terms, i));
    break;

  case BV64_POLY:
    result = fsubst_visit_bv64_poly(subst, bvpoly64_for_idx(terms, i));
    break;

  case BV_POLY:
    result = fsubst_visit_bv_poly(subst, bvpoly_for_idx(terms, i));
    break;

  case UNUSED_TERM:
  case RESERVED_TERM:
  default:
    assert(false);
    abort();
  }

  if (result) {
    /*
     * i is on a cycle of grey nodes:
     * x := ... -> y := u --> ... --> i --> ... --> x
     *
     * If remove_cycles is true, we'll remove the mapping y := u.
     * So we must clear the mark of all nodes on the path
     *   u --> ... --> i --> ... --> x (except x)
     */
    if (subst->remove_cycles) {
      mark_vector_add_mark(&subst->mark, i, MARK_WHITE);
    }
  } else {
    // i is not on a cycle and is now fully explored
    mark_vector_add_mark(&subst->mark, i, MARK_BLACK);
  }
  return result;
}

/*
 * Explore t:
 * - return true if t is on a cycle
 */
static bool fsubst_visit(full_subst_t *subst, term_t t) {
  int32_t i;
  uint8_t color;

  i = index_of(t);
  color = mark_vector_get_mark(&subst->mark, i);
  switch (color) {
  case MARK_WHITE: // not seen yet
    return fsubst_explore(subst, i);

  case MARK_GREY:
    // found a cycle
    return true;

  default:
    // already fully explored
    assert(color == MARK_BLACK);
    return false;
  }
}



/*
 * Check whether the map [x --> t] can be added to subst
 * - x and t must be be valid terms in subst->terms
 * - x must be an uninterpreted term
 *   t must be a ground term
 * - t's type must be a subtype of x's type
 *
 * - return false if x is already mapped to something else
 *   or if the map x --> t would create a cycle
 *
 * IMPORTANT: this assumes that there are no cycles in subst.
 * (otherwise the function may return false if there's a cycle
 * that does not include the edge x --> t).
 */
bool full_subst_check_map(full_subst_t *subst, term_t x, term_t t) {
  assert(good_map_types(subst, x, t));

  if (full_subst_is_mapped(subst, x)) {
    return false; // x already mapped
  }

  // check whether [x := t] creates a cycle
  subst->remove_cycles = false;   // detection only
  reset_mark_vector(&subst->mark);
  mark_vector_add_mark(&subst->mark, index_of(x), MARK_GREY);

  return !fsubst_visit(subst, t);
}


/*
 * Generalization of check_map:
 * - check whether one of a[0].. a[n-1] depends on x
 * - this can be used for checking whether a map of the form
 *   [x --> f(a[0]. ... a[n-1]) ]  will create a cycle.
 *
 * IMPORTANT: this assumes that there are no cycles in subst.
 * (otherwise the function may return false if there's a cycle
 * that does not include the edge x --> t).
 */
bool full_subst_check_deps(full_subst_t *subst, term_t x, uint32_t n, term_t *a) {
  uint32_t i;

  subst->remove_cycles = false;
  reset_mark_vector(&subst->mark);
  mark_vector_add_mark(&subst->mark, index_of(x), MARK_GREY);

  for (i=0; i<n; i++) {
    if (fsubst_visit(subst, a[i])) {
      /*
       * reached a grey node starting from a[i]
       * we assume that this node is x
       */
      return true;
    }
  }

  return false;
}


/*
 * Iterator: for collecting all x's in subst->map's domain
 * - aux is a vector
 * - p is a record from subst->map:
 *   p->key = uninterpreted term (i.e., x)
 *   p->val = what's mapped to x (i.e., a term t or NULL_TERM)
 */
static void collect_map(void *aux, const int_hmap_pair_t *p) {
  ivector_push(aux, p->key);
}

/*
 * Remove substitution cycles (if any)
 * - we do this in two steps:
 * - first collect all x's in subst->map
 * - then visit all these x's
 * This is safer since fsubst_visit may modify subst->map,
 * and subst->map should not be modified when we iterate
 * through it.
 */
void full_subst_remove_cycles(full_subst_t *subst) {
  ivector_t *v;
  uint32_t i, n;

  v = &subst->aux;
  ivector_reset(v);
  int_hmap_iterate(&subst->map, v, collect_map);

  subst->remove_cycles = true;
  reset_mark_vector(&subst->mark);
  n = v->size;
  for (i=0; i<n; i++) {
    (void) fsubst_visit(subst, v->data[i]);
  }
}


/*
 * Reset the internal cache:
 * - must be called if the substitution is modified by add_map
 *   after it's been applied (because the cache is no longer valid)
 */
void full_subst_clear_cache(full_subst_t *subst) {
  int_hmap_reset(&subst->cache);
}


/*
 * APPLY THE SUBSTITUTION
 */

/*
 * Check whether subst(t) is in the cache
 * - t must have positive polarity
 * - return subst(t) if it's there or NULL_TERM if it's not present
 */
static term_t cached_full_subst(full_subst_t *subst, term_t t) {
  int_hmap_pair_t *r;
  term_t s;

  assert(good_term(subst->terms, t) && is_pos_term(t));
  s = NULL_TERM;
  r = int_hmap_find(&subst->cache, t);
  if (r != NULL) {
    s = r->val;
    assert(good_term(subst->terms, s));
  }
  return s;
}

/*
 * Add [subst(t) = s] to the cache
 * - t must have positive polarity and subst(t) must not be present
 */
static void full_subst_cache_result(full_subst_t *subst, term_t t, term_t s) {
  int_hmap_pair_t *r;

  assert(good_term(subst->terms, t) && is_pos_term(t) &&  good_term(subst->terms, s));

  r = int_hmap_get(&subst->cache, t);
  assert(r->val < 0);
  r->val = s;
}


/*
 * Apply subst to term t
 * - t must be a valid term in subst->terms
 * - call longjmp if something goes wrong
 */
static term_t full_subst(full_subst_t *subst, term_t t);

/*
 * Apply subst to all children of composite d
 * - store the result in array a allocated in subst->stack
 */
static term_t *full_subst_children(full_subst_t *subst, composite_term_t *d) {
  term_t *a;
  uint32_t i, n;

  n = d->arity;
  a = alloc_istack_array(&subst->stack, n);
  for (i=0; i<n; i++) {
    a[i] = full_subst(subst, d->arg[i]);
  }

  return a;
}


/*
 * Apply subst to non-atomic terms
 */
// t == 0
static term_t full_subst_arith_eq(full_subst_t *subst, term_t t) {
  term_t s;

  s = full_subst(subst, t);
  return mk_arith_term_eq0(subst->mngr, s);
}

// t >= 0
static term_t full_subst_arith_ge(full_subst_t *subst, term_t t) {
  term_t s;

  s = full_subst(subst, t);
  return mk_arith_term_geq0(subst->mngr, s);
}

static term_t full_subst_ite(full_subst_t *subst, composite_term_t *ite) {
  term_table_t *tbl;
  term_t c, a, b, s;
  type_t tau;

  assert(ite->arity == 3);

  c = full_subst(subst, ite->arg[0]); // condition
  if (c == true_term) {
    s = full_subst(subst, ite->arg[1]);
  } else if (c == false_term) {
    s = full_subst(subst, ite->arg[2]);
  } else {
    a = full_subst(subst, ite->arg[1]);
    b = full_subst(subst, ite->arg[2]);

    tbl = subst->terms;
    tau = super_type(tbl->types, term_type(tbl, a), term_type(tbl, b));
    assert(tau != NULL_TYPE);

    s = mk_ite(subst->mngr, c, a, b, tau);
  }

  return s;
}

static term_t full_subst_app(full_subst_t *subst, composite_term_t *app) {
  term_t *a;
  term_t s;

  assert(app->arity >= 2);

  a = full_subst_children(subst, app);
  // a[0] = function, a[1 ... n-1] = arguments
  s = mk_application(subst->mngr, a[0], app->arity-1, a+1);
  free_istack_array(&subst->stack, a);

  // a[0] may be a lambda term so we apply beta-reduction here
  return beta_reduce(subst->mngr, s);
}

static term_t full_subst_update(full_subst_t *subst, composite_term_t *update) {
  term_t *a;
  term_t s;
  uint32_t n;

  assert(update->arity >= 3);
  a = full_subst_children(subst, update);
  n = update->arity;
  // a[0] = function, a[1 ... n-2] = arguments, a[n-1] = new value
  s = mk_update(subst->mngr, a[0], n-2, a+1, a[n-1]);
  free_istack_array(&subst->stack, a);

  return s;
}

static term_t full_subst_tuple(full_subst_t *subst, composite_term_t *tuple) {
  term_t *a;
  term_t s;

  a = full_subst_children(subst, tuple);
  s = mk_tuple(subst->mngr, tuple->arity, a);
  free_istack_array(&subst->stack, a);

  return s;
}

static term_t full_subst_eq(full_subst_t *subst, composite_term_t *eq) {
  term_t a, b;

  assert(eq->arity == 2);
  a = full_subst(subst, eq->arg[0]);
  b = full_subst(subst, eq->arg[1]);
  return mk_eq(subst->mngr, a, b);
}

static term_t full_subst_distinct(full_subst_t *subst, composite_term_t *distinct) {
  term_t *a;
  term_t s;

  a = full_subst_children(subst, distinct);
  s = mk_distinct(subst->mngr, distinct->arity, a);
  free_istack_array(&subst->stack, a);

  return s;
}

static term_t full_subst_forall(full_subst_t *subst, composite_term_t *forall) {
  term_t s;
  uint32_t n;

  n = forall->arity;
  assert(n >= 2);

  /*
   * Since subst maps unint to ground terms, there's no need to
   * worry about variable capture/renaming.
   * - forall->arg[0 ... n-2] are unchanged
   *   the body is subst(arg[n-1]).
   */
  s = full_subst(subst, forall->arg[n-1]);
  return mk_forall(subst->mngr, n-1, forall->arg, s);
}

static term_t full_subst_lambda(full_subst_t *subst, composite_term_t *lambda) {
  term_t s;
  uint32_t n;

  // as forall, no variable renaming required
  n = lambda->arity;
  assert(n >= 2);
  s = full_subst(subst, lambda->arg[n-1]);
  return mk_lambda(subst->mngr, n-1, lambda->arg, s);
}

static term_t full_subst_or(full_subst_t *subst, composite_term_t *or) {
  term_t *a;
  term_t s;
  uint32_t i, n;

  n = or->arity;
  assert(n >= 2);

  a = alloc_istack_array(&subst->stack, n);
  s = true_term;
  for (i=0; i<n; i++) {
    a[i] = full_subst(subst, or->arg[i]);
    if (a[i] == true_term) goto done;
  }

  s = mk_or(subst->mngr, n, a);

 done:
  free_istack_array(&subst->stack, a);

  return s;
}

static term_t full_subst_xor(full_subst_t *subst, composite_term_t *xor) {
  term_t *a;
  term_t s;

  assert(xor->arity >= 2);
  a = full_subst_children(subst, xor);
  s = mk_xor(subst->mngr, xor->arity, a);
  free_istack_array(&subst->stack, a);

  return s;
}

static term_t full_subst_arith_bineq(full_subst_t *subst, composite_term_t *eq) {
  term_t a, b;

  assert(eq->arity == 2);
  a = full_subst(subst, eq->arg[0]);
  b = full_subst(subst, eq->arg[1]);
  return mk_arith_eq(subst->mngr, a, b);
}

static term_t full_subst_bvarray(full_subst_t *subst, composite_term_t *bvarray) {
  term_t *a;
  term_t s;

  assert(bvarray->arity >= 1);
  a = full_subst_children(subst, bvarray);
  s = mk_bvarray(subst->mngr, bvarray->arity, a);
  free_istack_array(&subst->stack, a);

  return s;
}

static term_t full_subst_bvdiv(full_subst_t *subst, composite_term_t *div) {
  term_t a, b;

  assert(div->arity == 2);
  a = full_subst(subst, div->arg[0]);
  b = full_subst(subst, div->arg[1]);
  return mk_bvdiv(subst->mngr, a, b);
}

static term_t full_subst_bvrem(full_subst_t *subst, composite_term_t *rem) {
  term_t a, b;

  assert(rem->arity == 2);
  a = full_subst(subst, rem->arg[0]);
  b = full_subst(subst, rem->arg[1]);
  return mk_bvrem(subst->mngr, a, b);
}

static term_t full_subst_bvsdiv(full_subst_t *subst, composite_term_t *sdiv) {
  term_t a, b;

  assert(sdiv->arity == 2);
  a = full_subst(subst, sdiv->arg[0]);
  b = full_subst(subst, sdiv->arg[1]);
  return mk_bvsdiv(subst->mngr, a, b);
}

static term_t full_subst_bvsrem(full_subst_t *subst, composite_term_t *srem) {
  term_t a, b;

  assert(srem->arity == 2);
  a = full_subst(subst, srem->arg[0]);
  b = full_subst(subst, srem->arg[1]);
  return mk_bvsrem(subst->mngr, a, b);
}

static term_t full_subst_bvsmod(full_subst_t *subst, composite_term_t *smod) {
  term_t a, b;

  assert(smod->arity == 2);
  a = full_subst(subst, smod->arg[0]);
  b = full_subst(subst, smod->arg[1]);
  return mk_bvsmod(subst->mngr, a, b);
}

static term_t full_subst_bvshl(full_subst_t *subst, composite_term_t *shl) {
  term_t a, b;

  assert(shl->arity == 2);
  a = full_subst(subst, shl->arg[0]);
  b = full_subst(subst, shl->arg[1]);
  return mk_bvshl(subst->mngr, a, b);
}

static term_t full_subst_bvlshr(full_subst_t *subst, composite_term_t *lshr) {
  term_t a, b;

  assert(lshr->arity == 2);
  a = full_subst(subst, lshr->arg[0]);
  b = full_subst(subst, lshr->arg[1]);
  return mk_bvlshr(subst->mngr, a, b);
}

static term_t full_subst_bvashr(full_subst_t *subst, composite_term_t *ashr) {
  term_t a, b;

  assert(ashr->arity == 2);
  a = full_subst(subst, ashr->arg[0]);
  b = full_subst(subst, ashr->arg[1]);
  return mk_bvashr(subst->mngr, a, b);
}

static term_t full_subst_bveq(full_subst_t *subst, composite_term_t *eq) {
  term_t a, b;

  assert(eq->arity == 2);
  a = full_subst(subst, eq->arg[0]);
  b = full_subst(subst, eq->arg[1]);
  return mk_bveq(subst->mngr, a, b);
}

static term_t full_subst_bvge(full_subst_t *subst, composite_term_t *ge) {
  term_t a, b;

  assert(ge->arity == 2);
  a = full_subst(subst, ge->arg[0]);
  b = full_subst(subst, ge->arg[1]);
  return mk_bvge(subst->mngr, a, b);
}

static term_t full_subst_bvsge(full_subst_t *subst, composite_term_t *sge) {
  term_t a, b;

  assert(sge->arity == 2);
  a = full_subst(subst, sge->arg[0]);
  b = full_subst(subst, sge->arg[1]);
  return mk_bvsge(subst->mngr, a, b);
}


// select is not a safe pointer: we copy idx before the recursive call
static term_t full_subst_select(full_subst_t *subst, select_term_t *select) {
  uint32_t idx;
  term_t t;

  idx = select->idx;
  t = full_subst(subst, select->arg);
  return mk_select(subst->mngr, idx, t);
}

// bit is not a safe pointer
static term_t full_subst_bit(full_subst_t *subst, select_term_t *bit) {
  uint32_t idx;
  term_t t;

  idx = bit->idx;
  t = full_subst(subst, bit->arg);
  return mk_bitextract(subst->mngr, t, idx);
}


/*
 * POWER PRODUCTS
 */

/*
 * Check whether the product a[0]^e_0 ... a[n-1]^e_{n-1} has degree > YICES_MAX_DEGREE
 * - e_i = exponent in pprod p
 */
static bool pprod_degree_overflows(term_table_t *tbl, pprod_t *p, uint32_t n, term_t *a) {
  uint64_t d;
  uint32_t i;

  assert(n == p->len);

  d = 0;
  for (i=0; i<n; i++) {
    d += ((uint64_t) term_degree(tbl, a[i])) * p->prod[i].exp;
    if (d > (uint64_t) YICES_MAX_DEGREE) {
      return true;
    }
  }

  return false;
}


/*
 * Check whether term t is 0
 * - t is either an arithmetic or a bitvector term
 */
static bool term_is_zero(term_table_t *tbl, term_t t) {
  bvconst_term_t *c;
  uint32_t k;

  assert(is_arithmetic_term(tbl, t) || is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case ARITH_CONSTANT:
    assert(t == zero_term || q_is_nonzero(rational_term_desc(tbl, t)));;
    return t == zero_term;

  case BV64_CONSTANT:
    return bvconst64_term_desc(tbl, t)->value == (uint64_t) 0;

  case BV_CONSTANT:
    c = bvconst_term_desc(tbl, t);
    k = (c->bitsize + 31) >> 5;
    return bvconst_is_zero(c->data, k);

  default:
    return false;
  }
}


/*
 * Substitution for power product p
 */
static term_t full_subst_pprod(full_subst_t *subst, pprod_t *p) {
  term_t *a;
  term_t s;
  uint32_t i, n;

  n = p->len;
  a = alloc_istack_array(&subst->stack, n);
  for (i=0; i<n; i++) {
    a[i] = full_subst(subst, p->prod[i].var);
    if (term_is_zero(subst->terms, a[i])) {
      // the result is 0
      s = a[i];
      goto done;
    }
  }

  if (pprod_degree_overflows(subst->terms, p, n, a)) {
    longjmp(subst->env, FULL_SUBST_DEGREE_OVERFLOW);
  }

  s = mk_pprod(subst->mngr, p, n, a);

 done:
  free_istack_array(&subst->stack, a);

  return s;
}



/*
 * Arithmetic polynomial
 */
static term_t full_subst_poly(full_subst_t *subst, polynomial_t *p) {
  term_t *a;
  term_t s;
  uint32_t i, n;

  n = p->nterms;
  a = alloc_istack_array(&subst->stack, n);

  // skip the constant term if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[i] = const_idx;
    i ++;
  }

  // rest of the terms in p
  while (i < n) {
    a[i] = full_subst(subst, p->mono[i].var);
    i ++;
  }

  // build the polynomial
  s = mk_arith_poly(subst->mngr, p, n, a);

  free_istack_array(&subst->stack, a);

  return s;
}


/*
 * Bitvector polynomial: 64bit coefficients
 */
static term_t full_subst_bvpoly64(full_subst_t *subst, bvpoly64_t *p) {
  term_t *a;
  term_t s;
  uint32_t i, n;

  n = p->nterms;
  a = alloc_istack_array(&subst->stack, n);

  // skip the constant term if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[i] = const_idx;
    i ++;
  }

  // rest of the terms in p
  while (i < n) {
    a[i] = full_subst(subst, p->mono[i].var);
    i ++;
  }

  // build the polynomial
  s = mk_bvarith64_poly(subst->mngr, p, n, a);

  free_istack_array(&subst->stack, a);

  return s;
}


/*
 * Bitvector polynomial: more than 64bits
 */
static term_t full_subst_bvpoly(full_subst_t *subst, bvpoly_t *p) {
  term_t *a;
  term_t s;
  uint32_t i, n;

  n = p->nterms;
  a = alloc_istack_array(&subst->stack, n);

  // skip the constant term if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[i] = const_idx;
    i ++;
  }

  // rest of the terms in p
  while (i < n) {
    a[i] = full_subst(subst, p->mono[i].var);
    i ++;
  }

  // build the polynomial
  s= mk_bvarith_poly(subst->mngr, p, n, a);

  free_istack_array(&subst->stack, a);

  return s;
}





/*
 * Substitution for a composite term t
 * - t is a good term with positive polarity
 */
static term_t full_subst_composite(full_subst_t *subst, term_t t) {
  term_table_t *terms;
  term_t s;

  terms = subst->terms;
  switch (term_kind(terms, t)) {
  case ARITH_EQ_ATOM:
    s = full_subst_arith_eq(subst, arith_eq_arg(terms, t));
    break;

  case ARITH_GE_ATOM:
    s = full_subst_arith_ge(subst, arith_ge_arg(terms, t));
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
    s = full_subst_ite(subst, ite_term_desc(terms, t));
    break;

  case APP_TERM:
    s = full_subst_app(subst, app_term_desc(terms, t));
    break;

  case UPDATE_TERM:
    s = full_subst_update(subst, update_term_desc(terms, t));
    break;

  case TUPLE_TERM:
    s = full_subst_tuple(subst, tuple_term_desc(terms, t));
    break;

  case EQ_TERM:
    s = full_subst_eq(subst, eq_term_desc(terms, t));
    break;

  case DISTINCT_TERM:
    s = full_subst_distinct(subst, distinct_term_desc(terms, t));
    break;

  case FORALL_TERM:
    s = full_subst_forall(subst, forall_term_desc(terms, t));
    break;

  case LAMBDA_TERM:
    s = full_subst_lambda(subst, lambda_term_desc(terms, t));
    break;

  case OR_TERM:
    s = full_subst_or(subst, or_term_desc(terms, t));
    break;

  case XOR_TERM:
    s = full_subst_xor(subst, xor_term_desc(terms, t));
    break;

  case ARITH_BINEQ_ATOM:
    s = full_subst_arith_bineq(subst, arith_bineq_atom_desc(terms, t));
    break;

  case BV_ARRAY:
    s = full_subst_bvarray(subst, bvarray_term_desc(terms, t));
    break;

  case BV_DIV:
    s = full_subst_bvdiv(subst, bvdiv_term_desc(terms, t));
    break;

  case BV_REM:
    s = full_subst_bvrem(subst, bvrem_term_desc(terms, t));
    break;

  case BV_SDIV:
    s = full_subst_bvsdiv(subst, bvsdiv_term_desc(terms, t));
    break;

  case BV_SREM:
    s = full_subst_bvsrem(subst, bvsrem_term_desc(terms, t));
    break;

  case BV_SMOD:
    s = full_subst_bvsmod(subst, bvsmod_term_desc(terms, t));
    break;

  case BV_SHL:
    s = full_subst_bvshl(subst, bvshl_term_desc(terms, t));
    break;

  case BV_LSHR:
    s = full_subst_bvlshr(subst, bvlshr_term_desc(terms, t));
    break;

  case BV_ASHR:
    s = full_subst_bvashr(subst, bvashr_term_desc(terms, t));
    break;

  case BV_EQ_ATOM:
    s = full_subst_bveq(subst, bveq_atom_desc(terms, t));
    break;

  case BV_GE_ATOM:
    s = full_subst_bvge(subst, bvge_atom_desc(terms, t));
    break;

  case BV_SGE_ATOM:
    s = full_subst_bvsge(subst, bvsge_atom_desc(terms, t));
    break;

  case SELECT_TERM:
    s = full_subst_select(subst, select_term_desc(terms, t));
    break;

  case BIT_TERM:
    s = full_subst_bit(subst, bit_term_desc(terms, t));
    break;

  case POWER_PRODUCT:
    s = full_subst_pprod(subst, pprod_term_desc(terms, t));
    break;

  case ARITH_POLY:
    s = full_subst_poly(subst, poly_term_desc(terms, t));
    break;

  case BV64_POLY:
    s = full_subst_bvpoly64(subst, bvpoly64_term_desc(terms, t));
    break;

  case BV_POLY:
    s = full_subst_bvpoly(subst, bvpoly_term_desc(terms, t));
    break;

  default:
    assert(false);
    longjmp(subst->env, FULL_SUBST_INTERNAL_ERROR);
    break;
  }

  return s;
}


/*
 * Apply subst to term t
 * - t must be a valid term in subst->terms
 * - raise an exception via longjmp is something goes wrong
 */
static term_t full_subst(full_subst_t *subst, term_t t) {
  term_table_t *terms;
  uint32_t polarity;
  term_t r, s;

  polarity = polarity_of(t);
  t = unsigned_term(t);

  terms = subst->terms;

  switch (term_kind(terms, t)) {
  case CONSTANT_TERM:
  case ARITH_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
  case VARIABLE:
    s = t;
    break;

  case UNINTERPRETED_TERM:
    r = full_subst_get_map(subst, t);
    s = t;
    if (r >= 0) {
      // t mapped to r in subst->map
      s = full_subst(subst, r);
    }
    break;

  case UNUSED_TERM:
  case RESERVED_TERM:
    assert(false);
    longjmp(subst->env, FULL_SUBST_INTERNAL_ERROR);
    break;

  default:
    // t is a composite
    s = cached_full_subst(subst, t);
    if (s < 0) {
      s = full_subst_composite(subst, t);
      full_subst_cache_result(subst, t, s);
    }
    break;
  }


  return s ^ polarity;
}



/*
 * Apply subst to term t
 * - t must be a valid term in subst->terms
 * - the returned value is negative (error code) if something goes
 *   wrong.
 */
term_t full_subst_apply(full_subst_t *subst, term_t t) {
  term_t result;
  int code;

  code = setjmp(subst->env);
  if (code == 0) {
    result = full_subst(subst, t);
  } else {
    // error code
    assert(code < 0);
    result = (term_t) code;

    // clean up
    reset_istack(&subst->stack);
  }

  return result;
}
