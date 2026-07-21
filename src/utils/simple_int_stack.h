/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * STACK OF INTEGERS
 */

#ifndef __SIMPLE_INT_STACK_H
#define __SIMPLE_INT_STACK_H

#include <stdbool.h>
#include <stdint.h>

/*
 * Stack of integers organized by levels
 * - data = stack content = array of integers
 * - level = array of indices in increasing order
 * - top = top of the stack
 * - size = size of the data array
 * - nlevels = number of levels
 * - level_size = size of the level array
 * 
 * Stack content:
 * - data[0 ...  top-1] = all the integers
 * - level[0 ... nlevels - 1] = indices in increasing order
 *   such that level[i] = top of level i in the data array = start of level i+1
 * - if nlevels = n then data is split into n+1 slices:
 *   level 0: data[0 ... level[0] - 1]
 *   level i: data[level[i-1] ... level[i] - 1] for (0 < i < n)
 *   level n: data[level[n-1] ... top - 1]
 */
typedef struct {
  int32_t *data;
  uint32_t *level;
  uint32_t top;
  uint32_t size;
  uint32_t nlevels;
  uint32_t level_size;
} simple_istack_t;

#define DEF_SIMPLE_ISTACK_SIZE 1024
#define MAX_SIMPLE_ISTACK_SIZE (UINT32_MAX/sizeof(int32_t))
#define DEF_SIMPLE_ISTACK_LEVELS 128
#define MAX_SIMPLE_ISTACK_LEVELS (UINT32_MAX/sizeof(uint32_t))


/*
 * Initialize: empty stack, nothing allocated yet
 */
extern void init_simple_istack(simple_istack_t *stack);

/*
 * Reset to the empty  stack
 */
extern void reset_simple_istack(simple_istack_t *stack);

/*
 * Delete: free memory
 */
extern void  delete_simple_istack(simple_istack_t *stack);

/*
 * Check whether the stack is empty
 */
static inline bool simple_istack_is_empty(simple_istack_t *stack) {
  return stack->top == 0;
}

/*
 * Add x on the stack (at the current level)
 */
extern void simple_istack_add(simple_istack_t *stack, int32_t x);

/*
 * Start a new level
 */
extern void simple_istack_push(simple_istack_t *stack);

/*
 * Close the top-level and remove all its elements from the stack.
 * - nlevels must be positive
 */
extern void simple_istack_pop(simple_istack_t *stack);

/*
 * Backtrack to level l
 * - must have 0 <= l <= stack->nlevels
 */
extern void simple_istack_pop_to_level(simple_istack_t *stack, uint32_t l);


#endif /* __SIMPLE_INT_STACK_H */

