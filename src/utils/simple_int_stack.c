/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * STACK OF INTEGERS
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/simple_int_stack.h"

/*
 * Initialize: empty stack, nothing allocated yet
 */
void init_simple_istack(simple_istack_t *stack) {
  stack->data = NULL;
  stack->level = NULL;
  stack->top = 0;
  stack->size = 0;
  stack->nlevels = 0;
  stack->level_size = 0;
}

/*
 * Reset to the empty stack
 */
void reset_simple_istack(simple_istack_t *stack) {
  stack->top = 0;
  stack->nlevels = 0;
}

/*
 * Free memory
 */
void delete_simple_istack(simple_istack_t *stack) {
  safe_free(stack->data);
  safe_free(stack->level);
  stack->data = NULL;
  stack->level = NULL;
}


/*
 * Make room for more data
 */
static void simple_istack_more_data(simple_istack_t *stack) {
  uint32_t n;

  n = stack->size;
  if (n == 0) {
    // first allocation
    n = DEF_SIMPLE_ISTACK_SIZE;
    assert(n <= MAX_SIMPLE_ISTACK_SIZE);
    stack->data = (int32_t *) safe_malloc(n * sizeof(int32_t));
    stack->size = n;
  } else if (n < MAX_SIMPLE_ISTACK_SIZE) {
    // increase by 50%
    n += (n >> 1);
    assert(n > stack->size);
    if (n > MAX_SIMPLE_ISTACK_SIZE) {
      n = MAX_SIMPLE_ISTACK_SIZE;
    }
    stack->data = (int32_t *) safe_realloc(stack->data, n * sizeof(int32_t));
    stack->size = n;
  } else {
    assert(n == MAX_SIMPLE_ISTACK_SIZE);
    out_of_memory();
  }
}

/*
 * Make room for more levels
 */
static void simple_istack_more_levels(simple_istack_t *stack) {
  uint32_t n;

  n = stack->level_size;
  if (n == 0) {
    // first allocation
    n = DEF_SIMPLE_ISTACK_LEVELS;
    assert(n <= MAX_SIMPLE_ISTACK_LEVELS);
    stack->level = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
    stack->level_size = n;
  } else if (n < MAX_SIMPLE_ISTACK_LEVELS) {
    // increase by 50%
    n += (n >> 1);
    assert(n > stack->level_size);
    if (n > MAX_SIMPLE_ISTACK_LEVELS) {
      n = MAX_SIMPLE_ISTACK_LEVELS;
    }
    stack->level = (uint32_t *) safe_realloc(stack->level, n * sizeof(uint32_t));
    stack->level_size = n;
  } else {
    assert(n == MAX_SIMPLE_ISTACK_LEVELS);
    out_of_memory();
  }
}


/*
 * Add x on top of the stack
 */
void simple_istack_add(simple_istack_t *stack, int32_t x) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    simple_istack_more_data(stack);
  }
  assert(i < stack->size);
  stack->data[i] = x;
  stack->top = i+1;
}

/*
 * Start a new level
 */
void simple_istack_push(simple_istack_t *stack) {
  uint32_t i;

  i = stack->nlevels;
  if (i == stack->level_size) {
    simple_istack_more_levels(stack);
  }
  assert(i < stack->level_size);
  stack->level[i] = stack->top;
  stack->nlevels = i + 1;
}


/*
 * Backtrack to level l: 0 <= l < stack->nlevels
 */
static void simple_istack_do_pop(simple_istack_t *stack, uint32_t l) {
  assert(l < stack->nlevels);
  stack->top = stack->level[l];
  stack->nlevels = l;
}

/*
 * Close the top-level and remove all its elements from the stack.
 * - nlevels must be positive
 */
void simple_istack_pop(simple_istack_t *stack) {
  assert(stack->nlevels > 0);
  simple_istack_do_pop(stack, stack->nlevels - 1);
}

/*
 * Backtrack to level l
 * - must have 0 <= l <= stack->nlevels
 */
void simple_istack_pop_to_level(simple_istack_t *stack, uint32_t l) {
  assert(l <= stack->nlevels);
  if (l < stack->nlevels) {
    simple_istack_do_pop(stack, l);
  }
}



