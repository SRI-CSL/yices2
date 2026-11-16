/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * INSTRUCTION STACK FOR E-MATCHING
 */

#include "solvers/quant/ematch_instr_stack.h"


/*********************
 *   EMATCH STACK  *
 ********************/

/*
 * Initialize the stack
 */
void init_ematch_stack(ematch_stack_t *stack) {
  assert(DEF_EMATCH_STACK_SIZE < MAX_EMATCH_STACK_SIZE);

  stack->size = DEF_EMATCH_STACK_SIZE;
  stack->top = 0;
  stack->data = (int32_t *) safe_malloc(DEF_EMATCH_STACK_SIZE * sizeof(int32_t));
}


/*
 * Make the stack 50% larger
 */
static void extend_ematch_stack(ematch_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n >> 1;
  if (n >= MAX_EMATCH_STACK_SIZE) {
    out_of_memory();
  }

  stack->data = (int32_t *) safe_realloc(stack->data, n * sizeof(int32_t));
  stack->size = n;
}


/*
 * Empty the stack
 */
void reset_ematch_stack(ematch_stack_t *stack) {
  stack->top = 0;
}


/*
 * Delete the stack
 */
void delete_ematch_stack(ematch_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Save data for the current top element:
 */
void ematch_stack_save(ematch_stack_t *stack, int32_t idx) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_ematch_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i] = idx;
  stack->top = i + 1;
}


/*
 * Get the top record
 */
int32_t ematch_stack_top(ematch_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data[stack->top - 1];
}


/*
 * Remove the top record
 */
void ematch_stack_pop(ematch_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}

