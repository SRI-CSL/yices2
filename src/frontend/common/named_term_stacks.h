/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
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
 * Stack to deal with named terms
 * SMT2 has expressions like (! <term> :named xxx)
 * - if <term> is Boolean, then we must keep track of the pair <term> <name>
 *   to implement the command (get-assignments).
 * - when we support unsat cores, we'll have to also keep track of named
 *   named assertions (i.e. (assert (! <term> :named yyy)))
 *
 * We keep track of named assertions and named booleans in two stacks
 * of pairs (name, term). These pairs must be removed after (pop ...).
 */

#ifndef __NAMED_TERM_STACKS_H
#define __NAMED_TERM_STACKS_H

#include <stdint.h>

#include "terms/terms.h"

typedef struct named_term_s {
  term_t term;
  char *name;
} named_term_t;

typedef struct named_term_stack_s {
  named_term_t *data;
  uint32_t top;
  uint32_t size;
} named_term_stack_t;

#define DEF_NAMED_TERM_STACK_SIZE 256
#define MAX_NAMED_TERM_STACK_SIZE (UINT32_MAX/sizeof(named_term_t))


/*
 * Initialize: nothing is allocated yet
 */
extern void init_named_term_stack(named_term_stack_t *s);

/*
 * Push the pair <t, name>
 * - name must be a refcount string
 * - its reference counter is incremented
 */
extern void push_named_term(named_term_stack_t *s, term_t t, char *name);

/*
 * Remove pairs from the stack s
 * - n = new top: all pairs in s->data[0 ... n-1] are kept
 */
extern void pop_named_terms(named_term_stack_t *s, uint32_t n);

/*
 * Deletion: decrement refcounters for all the names
 * - then delete the stack (frees memory)
 */
extern void delete_named_term_stack(named_term_stack_t *s);

/*
 * Reset: remove all names then re-initialize
 */
extern void reset_named_term_stack(named_term_stack_t *s);


/*
 * Top pointer
 */
static inline uint32_t named_term_stack_top(const named_term_stack_t *s) {
  return s->top;
}


/*
 * Check whether it's empty
 */
static inline bool named_term_stack_is_empty(const named_term_stack_t *s) {
  return s->top == 0;
}



#endif /* __NAMED_TERM_STACKS_H */
