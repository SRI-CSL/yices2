/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * STACK FOR INTERNALIZATION OF NESTED IF-THEN-ELSE TERMS
 */

#include <assert.h>

#include "context/ite_flattener.h"

/*
 * Initialization
 */
void init_ite_flattener(ite_flattener_t *f) {
  init_ite_stack(&f->stack);
  init_ivector(&f->clause, 20);

  assert(f->clause.size == f->stack.top);
}

/*
 * Reset: empty the stack and the clause
 */
void reset_ite_flattener(ite_flattener_t *f) {
  reset_ite_stack(&f->stack);
  ivector_reset(&f->clause);

  assert(f->clause.size == f->stack.top);
}


/*
 * Free memory
 */
void delete_ite_flattener(ite_flattener_t *f) {
  delete_ite_stack(&f->stack);
  delete_ivector(&f->clause);
}

/*
 * Push an if-then-else descriptor + a literal
 * - the descriptor must have arity 3 (for a term (ite c a b)
 * - l should be the internalization of the term c
 */
void ite_flattener_push(ite_flattener_t *f, composite_term_t *d, literal_t l) {
  ite_stack_push(&f->stack, d);
  ivector_push(&f->clause, l);

  assert(f->clause.size == f->stack.top);
}


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
void ite_flattener_next_branch(ite_flattener_t *f) {
  uint32_t n;

  ite_stack_next_branch(&f->stack);
  n = ite_stack_depth(&f->stack);
  ivector_shrink(&f->clause, n);
  if (n > 0) {
    // flip the polarity of the last literal in the clause
    f->clause.data[n - 1] ^= 1;
  }

  assert(f->clause.size == f->stack.top);
}


/*
 * Check whether the current branch is live.
 * - it's considered dead if the one of the branch conditions 
 *   stored in f->clause is false_literal
 */
bool ite_flattener_branch_is_live(ite_flattener_t *f) {
  uint32_t i, n;

  n = f->clause.size;
  for (i=0; i<n; i++) {
    if (f->clause.data[i] == false_literal) {
      return false;
    }
  }
  return true;
}


/*
 * Check whether the last literal on the branch is false
 * - the tree must not be empty
 */
bool ite_flattener_last_lit_false(ite_flattener_t *f) {
  uint32_t i;

  assert(f->clause.size > 0);

  i = f->clause.size - 1;
  return f->clause.data[i] == false_literal;
}

