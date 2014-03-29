/*
 * FULL SUBSTITUTION
 */

#include "full_subst.h"

/*
 * Marks for cycle detection
 */
enum {
  MRK_WHITE,
  MRK_GREY,
  MKR_BLACK,
};


/*
 * Initialization:
 * - mngr = term_manager to use
 */
void init_full_subst(full_subst_t *subst, term_manager_t *mngr) {
  subst->mngr = mngr;
  subst->terms = term_manager_get_terms(mngr);
  init_int_hmap(&subst->map, 0);
  init_mark_vector(&subst->mark, 0, (uint8_t) MRK_WHITE);
  init_int_queue(&subst->queue, 0);
  init_int_hmap(&subst->cache, 0);
  init_istack(&subst->stack);
}


/*
 * Delete the whole thing
 */
void delete_full_subst(full_subst_t *subst) {
  delete_int_hmap(&subst->map);
  delete_mark_vector(&subst->mark);
  delete_int_queue(&subst->queue);
  delete_int_hmap(&subst->cache);
  delete_istack(&subst->stack);
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


