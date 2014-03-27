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

#include "int_queues.h"
#include "int_stack.h"
#include "mark_vector.h"
#include "int_hash_maps.h"
#include "terms.h"
#include "term_manager.h"

/*
 * Structure:
 * - mngr = relevant term manager
 * - terms = relevant term table (must be mngr->terms)
 * - map = substitution (uninterpreted terms to terms)
 * - mark = for cycle detection/removal
 * - queue = for cycle detection/removal
 * - cache = when applying the substitution
 * - stack = for allocation of arrays to store intermediate results
 * - env = to report exceptions
 */
typedef struct full_subst_s {
  term_manager_t *mngr;
  term_table_t *terms;
  int_hmap_t map;
  mark_vector_t mark;
  int_queue_t queue;
  int_hamp_t cache;
  int_stack_t stack;
  jmp_buf env;
} full_subst_t;


#endif /* __FULL_SUBST_H */


