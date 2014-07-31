/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STACK OF DISEQUALITIES
 */

/*
 * This is used by satellite solvers to keep track of disequalities
 * received from the egraph
 * - each element in the stacks is a disequality (x1 != x2) for two
 *   theory variables x1 and x2
 * - the stack is organized in successive frames. Each frame
 *   corresponds to a decision level.
 */

#ifndef __DISEQ_STACKS_H
#define __DISEQ_STACKS_H

#include <stdint.h>
#include <assert.h>

#include "solvers/egraph/egraph_base_types.h"

typedef struct diseq_s {
  thvar_t left, right;
} diseq_t;


/*
 * Asserted disequalities are stored in data[0 ... top-1]
 * - level_index[i] = value top when decision level i was entered
 * - if i < current decision level, disequalities asserted at level i
 *   are in data[k ... p-1] where k = level_index[i] and p = level_index[i+1]
 * - disequalities asserted at the current decision level i are in
 *   data[k ... top-1] where k = level_index[i]
 */
typedef struct diseq_stack_s {
  uint32_t size;      // size of array data
  uint32_t top;       // data[0 .. top-1] = the stack
  diseq_t *data;
  uint32_t *level_index;  // level_index[i] = value of top when decision level i was entered
  uint32_t nlevels;       // size of array level_index
} diseq_stack_t;


/*
 * Default and max sizes of arrays data and level_index
 */
#define DEF_DISEQ_STACK_SIZE 100
#define MAX_DISEQ_STACK_SIZE (UINT32_MAX/sizeof(diseq_t))

#define DEF_DISEQ_STACK_NLEVELS 100
#define MAX_DISEQ_STACK_NLEVELS (UINT32_MAX/sizeof(uint32_t))



/*
 * Initialize the stack
 * - use the default sizes for data and level_index
 * - the stack is empty
 */
extern void init_diseq_stack(diseq_stack_t *stack);


/*
 * Delete the stack: free memory
 */
extern void delete_diseq_stack(diseq_stack_t *stack);


/*
 * Empty the stack
 */
static inline void reset_diseq_stack(diseq_stack_t *stack) {
  stack->top = 0;
  assert(stack->level_index[0] == 0);
}


/*
 * Check whether the stack is empty
 */
static inline bool empty_diseq_stack(diseq_stack_t *stack) {
  return stack->top == 0;
}


/*
 * Start a new decision level:
 * - k = new level
 * IMPORTANT: k must be current decision level + 1
 */
extern void diseq_stack_increase_dlevel(diseq_stack_t *stack, uint32_t k);


/*
 * Push inequality (x != y) on top of the stack
 */
extern void diseq_stack_push(diseq_stack_t *stack, thvar_t x, thvar_t y);


/*
 * Backtrack to back_level:
 * - remove all disequalities asserted at level > back_level
 */
static inline void diseq_stack_backtrack(diseq_stack_t *stack, uint32_t back_level) {
  assert(back_level + 1 < stack->nlevels);
  stack->top = stack->level_index[back_level + 1];
}

#endif /* __DISEQ_STACKS_H */
