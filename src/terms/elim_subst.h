/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * VARIABLE ELIMINATION BY SUBSTITUTION
 */

/*
 * This extends full_subst.h to support variable elimination:
 * - the elim_subst structure includes a set of candidate variables Y
 *   (all elements of Y must be uninterpreted terms).
 * - it constructs a full_susbt by processing literals of the form
 *    (= y t) where y is a variable of Y and a term t
 *    (or literals that can be written in this forms).
 *
 * The set Y is stored as a int_hash_set.
 */

#ifndef __ELIM_SUBST_H
#define __ELIM_SUBST_H

#include <stdbool.h>

#include "utils/int_vectors.h"
#include "utils/int_hash_sets.h"
#include "terms/full_subst.h"


typedef struct elim_subst_s {
  term_manager_t *mngr;
  term_table_t *terms;
  int_hset_t *elimvars;
  full_subst_t full_subst;
  ivector_t aux;
} elim_subst_t;


/*
 * Initialize:
 * - mngr = term_manager
 * - elimvars = set of candidate for elimination
 */
extern void init_elim_subst(elim_subst_t *subst, term_manager_t *mngr, int_hset_t *elimvars);

/*
 * Delete the whole thing
 */
extern void delete_elim_subst(elim_subst_t *subst);

/*
 * Check whether f is equivalent to an equality (y == t)
 * where y is a candidate for elimination.
 * - if so, add map [y --> t] to the internal full_subst and return true
 * - otherwise, do nothing and return false.
 *
 * If check_cycles is true, we also check for subsitution cycles before
 * adding [y --> t] to the full_susbt, and returns false if there's a cycle.
 */
extern bool elim_subst_try_map(elim_subst_t *subst, term_t f, bool check_cycles);



/*
 * WRAPPERS FOR THE FUNCTIONS DEFINED IN FULL_SUBST
 */

/*
 * Remove cycles (if any)
 */
static inline void elim_subst_remove_cycles(elim_subst_t *subst) {
  full_subst_remove_cycles(&subst->full_subst);
}

/*
 * Apply the substitution to term t
 * - return a negative value if there's an error (error codes are defined in
 *   full_subst.h)
 */
static inline term_t elim_subst_apply(elim_subst_t *subst, term_t t) {
  return full_subst_apply(&subst->full_subst, t);
}

/*
 * Check whether x is mapped to something in subst
 * - x must be an uninterpreted term
 */
static inline bool elim_subst_is_mapped(elim_subst_t *subst, term_t x) {
  return full_subst_is_mapped(&subst->full_subst, x);
}

/*
 * Get the term mapped to x (return NULL_TERM = -1 if nothing is mapped)
 * - x must be an uninterpreted term
 */
static inline term_t elim_subst_get_map(elim_subst_t *subst, term_t x) {
  return full_subst_get_map(&subst->full_subst, x);
}



#endif /* __ELIM_SUBST_H */
