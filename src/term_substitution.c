/*
 * Data structure to support term substitution
 */

#include <assert.h>

#include "memalloc.h"
#include "term_substitution.h"

/*
 * Initialize subst: store the mapping v[i] --> t[i]
 */
void init_term_subst(term_subst_t *subst, term_table_t *ttbl, uint32_t n, term_t *v, term_t *t) {
  int_hmap_pair_t *p;
  uint32_t i;
  term_t x;

  subst->terms = ttbl;
  init_int_hmap(&subst->map, 0);
  init_subst_cache(&subst->cache);
  subst->rctx = NULL;
  subst->fvar = NULL;

  for (i=0; i<n; i++) {
    x = v[i];
    assert(term_kind(ttbl, x) == VARIABLE && good_term(ttbl, t[i]));
    p = int_hmap_get(&subst->map, x);
    p->val = t[i];
  }
}


/*
 * Get the renaming context. Allocate and initialize it if needed.
 */
static renaming_ctx_t *term_subst_get_rctx(term_subst_t *subst) {
  renaming_ctx_t *tmp;

  tmp = subst->rctx;
  if (tmp == NULL) {
    tmp = (renaming_ctx_t *) safe_malloc(sizeof(renaming_ctx_t));
    init_renaming_ctx(tmp, subst->terms, 0);
    subst->rctx = tmp;
  }

  return tmp;
}


/*
 * Get the variable collector: allocate and initialize it if needed
 */
static fvar_collector_t *term_subst_get_fvar(term_subst_t *subst) {
  fvar_collector_t *tmp;

  tmp = subst->fvar;
  if (tmp == NULL) {
    tmp = (fvar_collector_t *) safe_malloc(sizeof(fvar_collector_t));
    init_fvar_collector(tmp, subst->terms);
    subst->fvar = tmp;
  }

  return tmp;
}


/*
 * Delete: free all memory used
 */
void delete_term_subst(term_subst_t *subst) {
  delete_int_hmap(&subst->map);
  delete_subst_cache(&subst->cache);
  if (subst->rctx != NULL) {
    delete_renaming_ctx(subst->rctx);
    safe_free(subst->rctx);
    subst->rctx = NULL;
  }
  if (subst->fvar != NULL) {
    delete_fvar_collector(subst->fvar);
    safe_free(subst->fvar);
    subst->fvar = NULL;
  }
}


/*
 * Lookup the term mapped to x (taking renaming into account)
 * - x must be a variable
 * - if there's a renaming, lookup x in the renaming context
 * - if x is not renamed, lookup x in the map
 * - if x is not renamed and not in the map, then return x
 */
term_t get_subst_of_var(term_subst_t *subst, term_t x) {
  int_hmap_pair_t *p;
  term_t y;

  assert(term_kind(subst->terms, x) == VARIABLE);

  y = NULL_TERM;
  if (subst->rctx != NULL) {
    y = renaming_ctx_lookup(subst->rctx, x);
  }
  if (y == NULL_TERM) {
    p = int_hmap_find(&subst->map, x);
    y = x;
    if (p != NULL) {
      y = p->val;
    }
  }

  return y;
}


/*
 * Check whether the result of subst(t) is stored in the cache
 * - t must be a valid term in subst->terms
 * - this takes the renaming context into account
 * - return NULL_TERM (-1) is the result is not in the cache
 */
term_t get_cached_subst(term_subst_t *subst, term_t t) {
  renaming_ctx_t *ctx;
  harray_t *hashed_ctx;

  assert(good_term(subst->terms, t));

  hashed_ctx = NULL;
  ctx = subst->rctx;
  if (ctx != NULL && !renaming_ctx_is_empty(ctx)) {
    hashed_ctx = renaming_ctx_hash(ctx);
  }

  return subst_cache_lookup(&subst->cache, hashed_ctx, t);
} 


/*
 * Add u as subst(t) in the cache
 * - t and u must be valid terms in subst->terms
 * - there must not be an existing value for t in the cache
 * - this takes the renaming context into account (cf. subst_cache.h)
 */
void cache_subst_result(term_subst_t *subst, term_t t, term_t u) {
  renaming_ctx_t *ctx;
  harray_t *hashed_ctx;

  assert(good_term(subst->terms, t) && good_term(subst->terms, u));

  hashed_ctx = NULL;
  ctx = subst->rctx;
  if (ctx != NULL && !renaming_ctx_is_empty(ctx)) {
    hashed_ctx = renaming_ctx_hash(ctx);
  }

  subst_cache_add(&subst->cache, hashed_ctx, t, u);
}


/*
 * Extend the current renaming context: by renamings for v[0 .. n-1]
 * (cf. renaming_context.h)
 * - v[0] ... v[n-1] must all be variables in subst->terms
 * - this allocates and initializes the renaming data structure if needed
 */
void subst_push_renaming(term_subst_t *subst, uint32_t n, term_t *v) {
  renaming_ctx_t *ctx;

  ctx = term_subst_get_rctx(subst);
  renaming_ctx_push_vars(ctx, n, v);
}


/*
 * Remove the last n variable renaming (cf. renaming_context.h)
 * - the current renaming must exist and have at least n variables
 */
void subst_pop_renaming(term_subst_t *subst, uint32_t n) {
  assert(subst->rctx != NULL);
  renaming_ctx_pop_vars(subst->rctx, n);
}


/*
 * Check whether term t is ground
 * - t must be a valid term in subst->terms
 * - allocate and initialize the variable collector structure if needed
 */
bool subst_term_is_ground(term_subst_t *subst, term_t t) {
  fvar_collector_t *fvar;

  fvar = term_subst_get_fvar(subst);
  return term_is_ground(fvar, t);
}
