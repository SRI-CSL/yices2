/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>

#include "utils/ptr_stack.h"

static ptr_stack_t stack;

static void print_stack(ptr_stack_t *stack) {
  pblock_t *b;

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

int main() {
  void **a1, **a2, **a3, **a4;

  printf("=== Initialization ===\n");
  init_pstack(&stack);
  print_stack(&stack);

  printf("=== Allocation a1: size 100 ===\n");
  a1 = alloc_pstack_array(&stack, 100);
  printf("  a1 = %p\n", a1);
  print_stack(&stack);

  printf("=== Allocation a2: size 500 ===\n");
  a2 = alloc_pstack_array(&stack, 500);
  printf("  a2 = %p\n", a2);
  print_stack(&stack);

  printf("=== Allocation a3: size 800 ===\n");
  a3 = alloc_pstack_array(&stack, 800);
  printf("  a3 = %p\n", a3);
  print_stack(&stack);

  printf("=== Allocation a4: size 8000 ===\n");
  a4 = alloc_pstack_array(&stack, 8000);
  printf("  a4 = %p\n", a4);
  print_stack(&stack);

  printf("=== Free a4 ===\n");
  free_pstack_array(&stack, a4);
  print_stack(&stack);

  printf("=== Allocation a4: size 800 ===\n");
  a4 = alloc_pstack_array(&stack, 800);
  printf("  a4 = %p\n", a4);
  print_stack(&stack);

  printf("=== Free a4 ===\n");
  free_pstack_array(&stack, a4);
  print_stack(&stack);

  printf("=== Free a3 ===\n");
  free_pstack_array(&stack, a3);
  print_stack(&stack);

  printf("=== Reset ===\n");
  reset_pstack(&stack);
  print_stack(&stack);

  delete_pstack(&stack);
  return 0;
}
