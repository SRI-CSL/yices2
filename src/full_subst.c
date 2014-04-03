/*
 * FULL SUBSTITUTION
 */

#include "full_subst.h"

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
     * we'll remove the mapping y := u so we must clear the mark of
     * all nodes on the path u --> ... --> i --> ... --> x (except x)
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
 * -
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
 * - return false if x is already mapped to something else
 *   or if the map x --> t would create a cycle
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

