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

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>

#include "utils/int_stack.h"

static int_stack_t stack;

static void print_stack(int_stack_t *stack) {
  iblock_t *b;

  printf("stack %p\n", stack);
  printf("  current block = %p\n", stack->current);
  printf("  free list = %p\n", stack->free);

  printf("  active blocks:\n");
  b = stack->current;
  while (b != NULL) {
    printf("   block %p: size = %"PRIu32" ptr = %"PRIu32" data = %p\n", b, b->size, b->ptr, b->data);
    b = b->next;
  }

  printf("  free blocks:\n");
  b = stack->free;
  while (b != NULL) {
    printf("   block %p: size = %"PRIu32" ptr = %"PRIu32" data = %p\n", b, b->size, b->ptr, b->data);
    b = b->next;
  }
  printf("\n");
}

int main(void) {
  int32_t *a1, *a2, *a3, *a4;

  printf("=== Initialization ===\n");
  init_istack(&stack);
  print_stack(&stack);

  printf("=== Allocation a1: size 100 ===\n");
  a1 = alloc_istack_array(&stack, 100);
  printf("  a1 = %p\n", a1);
  print_stack(&stack);

  printf("=== Allocation a2: size 500 ===\n");
  a2 = alloc_istack_array(&stack, 500);
  printf("  a2 = %p\n", a2);
  print_stack(&stack);

  printf("=== Allocation a3: size 800 ===\n");
  a3 = alloc_istack_array(&stack, 800);
  printf("  a3 = %p\n", a3);
  print_stack(&stack);

  printf("=== Allocation a4: size 8000 ===\n");
  a4 = alloc_istack_array(&stack, 8000);
  printf("  a4 = %p\n", a4);
  print_stack(&stack);

  printf("=== Free a4 ===\n");
  free_istack_array(&stack, a4);
  print_stack(&stack);

  printf("=== Allocation a4: size 800 ===\n");
  a4 = alloc_istack_array(&stack, 800);
  printf("  a4 = %p\n", a4);
  print_stack(&stack);

  printf("=== Free a4 ===\n");
  free_istack_array(&stack, a4);
  print_stack(&stack);

  printf("=== Free a3 ===\n");
  free_istack_array(&stack, a3);
  print_stack(&stack);

  printf("=== Reset ===\n");
  reset_istack(&stack);
  print_stack(&stack);

  delete_istack(&stack);
  return 0;
}
