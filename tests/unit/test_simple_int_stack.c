/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
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

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>

#include "utils/simple_int_stack.h"

static void print_level(int32_t *data, uint32_t start, uint32_t end) {
  uint32_t i;

  printf("[");
  for (i=start; i<end; i++) {
    printf(" %"PRId32, data[i]);
  }
  printf(" ]\n");
}

static void print_stack(simple_istack_t *stack) {
  uint32_t i, j, n;

  printf("stack %p\n", stack);
  printf("  top = %"PRIu32"\n", stack->top);
  printf("  size = %"PRIu32"\n", stack->size);
  printf("  nlevels = %"PRIu32"\n", stack->nlevels);
  printf("  level_size = %"PRIu32"\n", stack->level_size);

  j = 0;
  n = stack->nlevels;
  for (i=0; i<n; i++) {
    printf("  level[%"PRIu32"]: ", i);
    print_level(stack->data, j, stack->level[i]);
    j = stack->level[i];
  }
  printf("  level[%"PRIu32"]: ", i);
  print_level(stack->data, j, stack->top);
  printf("---\n");
}

static simple_istack_t stack;

int main(void) {
  uint32_t i;
  int32_t x;

  init_simple_istack(&stack);
  printf("=== init ===\n");
  print_stack(&stack);

  for (i=0; i<10; i++) {
    x = i+1;
    simple_istack_add(&stack, x);
    simple_istack_add(&stack, x);
    simple_istack_add(&stack, x);
    simple_istack_add(&stack, x);
    simple_istack_push(&stack);
  }
  simple_istack_add(&stack, 20);
  simple_istack_add(&stack, 20);
  printf("=== 10 levels ===\n");
  print_stack(&stack);

  simple_istack_pop_to_level(&stack, 4);
  printf("=== pop to level 4 ===\n");
  print_stack(&stack);

  simple_istack_push(&stack);
  printf("=== empty push ===\n");
  print_stack(&stack);

  reset_simple_istack(&stack);
  printf("=== reset ===\n");
  print_stack(&stack);

  simple_istack_add(&stack, 0);
  simple_istack_push(&stack);
  simple_istack_add(&stack, 1);
  simple_istack_push(&stack);
  simple_istack_add(&stack, 2);
  simple_istack_push(&stack);
  simple_istack_add(&stack, 3);
  printf("=== three levels ===\n");
  print_stack(&stack);

  delete_simple_istack(&stack);

  return 0;
}
