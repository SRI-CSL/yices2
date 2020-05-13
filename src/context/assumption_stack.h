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
 * STACK TO STORE ASSUMPTIONS IN A CONTEXT
 */

/*
 * To deal with assumptions, the context provides three main 
 * functions:
 *
 * 1) add_assumption(context_t *ctx, term_t t) returns a literal
 *    (if this literal is set to true then term t is assumed in
 *     the context).
 *
 * 2) check_context_with_assumptions that take an array of assumed
 *    literals
 *
 * 3) context_build_unsat_core that computes an inconsistent subset
 *    of the assumed literals.
 *
 * To support this and properly work with push and pop, we use a
 * stack to store all assumptions and keep track of the term they
 * represent. Assumption literals are deleted on a call to push.
 */

#ifndef __ASSUMPTION_STACK_H
#define __ASSUMPTION_STACK_H

#include <stdint.h>

#include "solvers/cdcl/smt_core_base_types.h"
#include "terms/terms.h"


/*
 * Elements in the stack:
 * - term = assumed term (Boolean)
 * - lit = corresponding literal in the CDCL solver
 * - level = base level when the assumption was added
 */
typedef struct assumption_elem_s {
  term_t term;
  literal_t lit;
  uint32_t level;
} assumption_elem_t;


/*
 * Index structure:
 * - a hash table that maps term/literal to an int32 index
 * - size = size of the table (a power of 2)
 * - nelems = number of elements stored in the table
 * - ndeleted = number of deleted elements
 * - resize and cleanup thresholds
 */
typedef struct hash_index_s {
  int32_t *data;
  uint32_t size;
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} hash_index_t;

#define DEF_ASSUMPTION_INDEX_SIZE 64
#define MAX_ASSUMPTION_INDEX_SIZE (UINT32_MAX/sizeof(int32_t))

#define ASSUMPTION_INDEX_RESIZE_RATIO 0.65
#define ASSUMPTION_INDEX_CLEANUP_RATIO 0.20


/*
 * Stack + two indexes
 * - data = stack content
 * - size = size of the data array
 * - top = index of the top of the stack 
 *   the stack is data[0 ... top-1]
 * - level is incremented on push and decremented on pop
 *
 * - lit_index maps literal --> assumption element
 * - term_index maps terms  --> assumption element
 */
typedef struct assumption_stack_s {
  assumption_elem_t *data;
  hash_index_t lit_index;
  hash_index_t term_index;
  uint32_t size;
  uint32_t top;
  uint32_t level ;
} assumption_stack_t;

#define DEF_ASSUMPTION_STACK_SIZE 64
#define MAX_ASSUMPTION_STACK_SIZE (UINT32_MAX/sizeof(assumption_elem_t))


/*
 * Initialize the stack:
 * - nothing is allocated yet
 * - level is set to 0
 */
extern void init_assumption_stack(assumption_stack_t *stack);

/*
 * Free memory
 */
extern void delete_assumption_stack(assumption_stack_t *stack);

/*
 * Empty the stack and the index arrays
 */
extern void reset_assumption_stack(assumption_stack_t *stack);

/*
 * Start a new level
 */
static inline void assumption_stack_push(assumption_stack_t *stack) {
  stack->level ++;
}

/*
 * Close the current level and remove all assumptions added at this
 * level. stack->nlevels must be positive.
 */
extern void assumption_stack_pop(assumption_stack_t *stack);

/*
 * Add a pair (t, l) on top of the stack: at the current level
 */
extern void assumption_stack_add(assumption_stack_t *stack, term_t t, literal_t l);

/*
 * Search for a term t attached to literal l in the stack:
 * - this searches for an element of the form (t, l, k) in the stack
 *   and return t;
 * - if several terms are mapped to l, the function returns the first one
 *   (i.e., with the lowest level k).
 * - if there's no such element, the function returns NULL_TERM (i.e., -1)
 */
extern term_t assumption_term_for_literal(const assumption_stack_t *stack, literal_t l);

/*
 * Search for a literal l attached to term t in the stack:
 * - search for a triple (t, l, k) in the stack and return l
 * - return null_literal if there's no such triple
 */
extern literal_t assumption_literal_for_term(const assumption_stack_t *stack, term_t t);


#endif /* __ASSUMPTION_STACK_H */
