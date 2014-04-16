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

#include "int_hash_sets.h"
#include "full_subst.h"

typedef struct elim_subst_s {
  term_manager_t *mngr;
  term_table_t *terms;
  int_hset_t *elimvars;
  full_subst_t full_subst;
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
 */
extern bool elim_subst_try_map(elim_subst_t *subst, term_t f);

/*
 * Same thing but also check whether [y --> t] causes a substitution cycle
 * - if there's a cycle, the map is not added and the function returns false
 */
extern bool elim_subst_try_check_map(elim_subst_t *subst, term_t f);

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

#endif /* __ELIM_SUBST_H */
