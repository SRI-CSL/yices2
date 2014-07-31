/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * FULL SUBSTITUTION
 */

/*
 * A full substitution is intended to remove uninterpreted terms from
 * a formula or a term. It's a mapping from uninterpreted terms to
 * terms: { x_1 := t_1, ...., x_n := t_n }. It's allowed for x_i to
 * occur in t_j as long as this does not cause subsitution cycles.
 *
 * Unlike the standard substitution (in term_substitution.h), applying
 * a full substitution to t removes all instances of x_1, ..., x_n.
 *
 * Example
 * -------
 * If f is (p x y) and we want to replace x by (f y) and y by b
 * - the result for standard subst is (p (f y) b)
 * - the result for full subst is (p (f b) b)
 *
 * The full subst { x_1 := t_1, ..., x_n := t_n } is well defined
 * if there's no substitution cycles. Then applying it to a term t
 * is the same as repeatedly applying the standard/parallel substitution
 *    x_1 --> t_1, .... x_n --> t_n
 * until all x_i's are been removed.
 *
 * Restrictions:
 * -------------
 * To avoid issues with variable captures and renaming, the implementation
 * currently requires:
 * - all x_i's must be uninterpreted terms (can't be variables)
 * - all t_i's must be ground terms (don't contain free variables)
 *
 * Possible optimization
 * ---------------------
 * We can extract a substitution from an polynomial equation:
 * - if (a_0 + a_1 X_1 + ... + a_n X_n == 0) is asserted
 *   then we can turn it into the substitution
 *       X_1 := - a_0/a_1 - a_2/a_1 X_2 ... - a_n/a_1 X_n. *
 * This requires creating a polynomial term for
 *     - a_0/a_1 - a_2/a_1 X_2 ... - a_n/a_1 X_n,
 * which can be wasteful (for example, if this causes a
 * cycle).
 * We could avoid creating this temporary term by storing
 * the polynomial a_0 + a_1 X_1 + ... + a_n X_n as an
 * implicit definition of mapping for X_1 and delay the
 * construction of (-a_0/a_1 - ... ) after we remove cycles.
 */

#ifndef __FULL_SUBST_H
#define __FULL_SUBST_H

#include <stdint.h>
#include <stdbool.h>
#include <setjmp.h>

#include "utils/int_stack.h"
#include "utils/int_vectors.h"
#include "utils/mark_vectors.h"
#include "utils/int_hash_map.h"
#include "terms/terms.h"
#include "terms/term_manager.h"


/*
 * Error codes
 */
enum {
  FULL_SUBST_INTERNAL_ERROR = -2,   // Bug somewhere
  FULL_SUBST_DEGREE_OVERFLOW = -3,  // Overflow in the result
  FULL_SUBST_CYCLE = -4,            // Not used for now
};


/*
 * Structure:
 * - mngr = relevant term manager
 * - terms = relevant term table (must be mngr->terms)
 * - map = substitution (uninterpreted terms to terms)
 * - mark = for cycle detection/removal
 * - remove_cycles = boolean flag to distinguish between detection and removal of cycles
 * - cache = when applying the substitution
 * - stack = for allocation of arrays to store intermediate results
 * - aux = generic vector (buffer)
 * - env = to report exceptions
 */
typedef struct full_subst_s {
  term_manager_t *mngr;
  term_table_t *terms;
  int_hmap_t map;
  mark_vector_t mark;
  bool remove_cycles;
  int_hmap_t cache;
  int_stack_t stack;
  ivector_t aux;
  jmp_buf env;
} full_subst_t;


/*
 * Initialization:
 * - mngr = term_manager to use
 */
extern void init_full_subst(full_subst_t *subst, term_manager_t *mngr);


/*
 * Delete the whole thing
 */
extern void delete_full_subst(full_subst_t *subst);



/*
 * CONSTRUCTION
 */

/*
 * Check what's mapped to x
 * - x must be an uninterpreted term in subst->terms
 * - return  NULL_TERM if nothing is mapped to x
 */
extern term_t full_subst_get_map(full_subst_t *subst, term_t x);

/*
 * Check whether x is mapped to something
 */
static inline bool full_subst_is_mapped(full_subst_t *subst, term_t x) {
  return full_subst_get_map(subst, x) >= 0;
}

/*
 * Add mapping [x --> t] to subst
 * - x and t must be valid terms in subst->terms
 * - x must be an uninterpreted term
 *   t must be a ground term
 * - t's type must be a subtype of x's type
 * - x must not be mapped to anything yet
 */
extern void full_subst_add_map(full_subst_t *subst, term_t x, term_t t);

/*
 * Check whether the map [x --> t] can be added to subst
 * - x and t must be be valid terms in subst->terms
 * - x must be an uninterpreted term
 *   t must be a ground term
 * - t's type must be a subtype of x's type
 * - return false if x is already mapped to something else
 *   or if the map x --> t would create a cycle
 *
 * IMPORTANT: this assumes that there are no cycles in subst.
 * (otherwise the function may return false if there's a cycle
 *  that does not include the edge x --> t).
 */
extern bool full_subst_check_map(full_subst_t *subst, term_t x, term_t t);


/*
 * Check whether one of a[0].. a[n-1] depends on x
 * - return true if so, false otherwise
 *
 * This can be used for checking whether a map of the form
 *   [x --> f(a[0]. ... a[n-1]) ]  will create a cycle
 *
 * Important: subst must not contain cycles.
 */
extern bool full_subst_check_deps(full_subst_t *subst, term_t x, uint32_t n, term_t *a);


/*
 * Remove substitution cycles (if any)
 */
extern void full_subst_remove_cycles(full_subst_t *subst);



/*
 * APPLY TO TERMS
 */

/*
 * Apply subst to term t
 * - t must be a valid term in subst->terms
 * - the returned value is negative (error code) if something goes
 *   wrong.
 *
 * NOTE: on-the-fly detection of cycles is not implemented
 * - this means that error code FULL_SUBST_CYCLE is never returned
 * - so make sure there's no substitution cycles before calling
 *   this function.
 */
extern term_t full_subst_apply(full_subst_t *subst, term_t t);

/*
 * Reset the internal cache:
 * - must be called if the substitution is modified (by add_map)
 *   after it's been applied (because the cache is no longer valid)
 */
extern void full_subst_clear_cache(full_subst_t *subst);



#endif /* __FULL_SUBST_H */

