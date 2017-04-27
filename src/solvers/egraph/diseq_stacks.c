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
 * STACK OF DISEQUALITIES
 */

#include "solvers/egraph/diseq_stacks.h"
#include "utils/memalloc.h"

/*
 * Initialize the disequality stack
 */
void init_diseq_stack(diseq_stack_t *stack) {
  assert(DEF_DISEQ_STACK_SIZE < MAX_DISEQ_STACK_SIZE &&
         0 < DEF_DISEQ_STACK_NLEVELS &&
         DEF_DISEQ_STACK_NLEVELS < MAX_DISEQ_STACK_NLEVELS);

  stack->size = DEF_DISEQ_STACK_SIZE;
  stack->top = 0;
  stack->data = (diseq_t *) safe_malloc(DEF_DISEQ_STACK_SIZE * sizeof(diseq_t));

  stack->level_index = (uint32_t *) safe_malloc(DEF_DISEQ_STACK_NLEVELS * sizeof(uint32_t));
  stack->nlevels = DEF_DISEQ_STACK_NLEVELS;
  stack->level_index[0] = 0;
}


/*
 * Make the stack larger by 50%
 */
static void extend_diseq_stack(diseq_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n >> 1;
  if (n >= MAX_DISEQ_STACK_SIZE) {
    out_of_memory();
  }

  stack->data = (diseq_t *) safe_realloc(stack->data, n * sizeof(diseq_t));
  stack->size = n;
}


/*
 * Make the level_index array larger by 50%
 */
static void extend_diseq_stack_levels(diseq_stack_t *stack) {
  uint32_t n;

  n = stack->nlevels + 1;
  n += n>>1;
  if (n >= MAX_DISEQ_STACK_NLEVELS) {
    out_of_memory();
  }

  stack->level_index = (uint32_t *) safe_realloc(stack->level_index, n * sizeof(uint32_t));
  stack->nlevels = n;
}


/*
 * Delete the stack
 */
void delete_diseq_stack(diseq_stack_t *stack) {
  safe_free(stack->data);
  safe_free(stack->level_index);
  stack->data = NULL;
  stack->level_index = NULL;
}


/*
 * Start a new decision level:
 * - k = new level
 */
void diseq_stack_increase_dlevel(diseq_stack_t *stack, uint32_t k) {
  if (stack->nlevels == k) {
    extend_diseq_stack_levels(stack);
  }
  assert(k < stack->nlevels);
  stack->level_index[k] = stack->top;
}



/*
 * Push inequality (x != y) on top of the stack
 */
void diseq_stack_push(diseq_stack_t *stack, thvar_t x, thvar_t y) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_diseq_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].left = x;
  stack->data[i].right = y;
  stack->top = i+1;
}


