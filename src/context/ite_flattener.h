/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STACK FOR INTERNALIZATION OF NESTED IF-THEN-ELSE TERMS
 */

/*
 * This is intended to help convert nested if-then-else terms to
 * arithmetic or egraph terms while avoiding unecessary intermediate
 * variables.
 *
 * Example: given a term (ite c1 (ite c2 a2 b2) (ite c3 a3 b3))
 * the simplest translation uses a variable for each if-then-else:
 *    x2 = (ite c2 a2 b2)
 *    x3 = (ite c3 a3 b3)
 *    x1 = (ite c1 x2 x3)
 *
 * This gives the following clause:
 *         c2  => x2 = a2
 *    (not c2) => x2 = b2
 *         c3  => x3 = a3
 *    (not c3) => x3 = b3
 *         c1  => x1 = x2
 *    (not c1) => x1 = x3
 *
 * An alternative is to eliminate x2 and x3 and use fewer clauses
 *                 c1 and c2  => x1 = a2
 *            c1 and (not c2) => x1 = b2
 *            (not c1) and c3 => x1 = a3
 *      (not c1) and (not c3) => x1 = b3
 *
 * To support this translation, we use a stack of if-then-else terms +
 * a stack of literals (to capture the conditions c_i).
 */

#ifndef __ITE_FLATTENER_H
#define __ITE_FLATTENER_H

#include <stdint.h>
#include <stdbool.h>

#include "solvers/cdcl/smt_core_base_types.h"
#include "terms/ite_stack.h"
#include "utils/int_vectors.h"


/*
 * Data structure: if-then-else stack + vector of literals
 */
typedef struct ite_flattener_s {
  ite_stack_t stack;
  ivector_t clause;
} ite_flattener_t;


/*
 * Initialization
 */
extern void init_ite_flattener(ite_flattener_t *f);

/*
 * Reset: empty the stack and the clause
 */
extern void reset_ite_flattener(ite_flattener_t *f);

/*
 * Free memory
 */
extern void delete_ite_flattener(ite_flattener_t *f);

/*
 * Push an if-then-else descriptor + a literal
 * - the descriptor must have arity 3 (for a term (ite c a b)
 * - l should be the internalization of the term c
 */
extern void ite_flattener_push(ite_flattener_t *f, composite_term_t *d, literal_t l);


/*
 * Move to the next branch
 * - this updates the stack to point to the next branch (not fully explored yet)
 * - the leaf is set to the last term in this branch
 * - the clause is updated (by flipping the polarity of the last literal on
 *   the new branch).
 *
 * This may empty the stack: in which case, clause is reset and the leaf is
 * set the NULL_TERM.
 */
extern void ite_flattener_next_branch(ite_flattener_t *f);


/*
 * Check whether the current branch is live.
 * - it's considered dead if the one of the branch conditions 
 *   stored in f->clause is false_literal
 */
extern bool ite_flattener_branch_is_live(ite_flattener_t *f);


/*
 * Check whether the last literal on the branch is false
 * - the tree must not be empty
 */
extern bool ite_flattener_last_lit_false(ite_flattener_t *f);


/*
 * Export the current clause
 * - adds all the literals into vector v
 * - the vector v is not reset
 */
static inline void ite_flattener_get_clause(ite_flattener_t *f, ivector_t *v) {
  ivector_add(v, f->clause.data, f->clause.size);
}


/*
 * Check emptiness and get depth (inherited from ite_stack)
 */
static inline bool ite_flattener_is_empty(ite_flattener_t *f) {
  return ite_stack_is_empty(&f->stack);
}

static inline bool ite_flattener_is_nonempty(ite_flattener_t *f) {
  return ite_stack_is_nonempty(&f->stack);
}

static inline bool ite_flattener_depth(ite_flattener_t *f) {
  return ite_stack_depth(&f->stack);
}

// current leaf (maybe NULL_TERM if the stack is empty)
static inline term_t ite_flattener_leaf(ite_flattener_t *f) {
  return f->stack.leaf;
}


#endif /* __ITE_FLATTENER_H */
