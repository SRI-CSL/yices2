/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test arena allocator
 */

#include <stdio.h>
#include <inttypes.h>
#include "utils/arena.h"

static void print_arena(arena_t *a) {
  printf("--- Arena %p ---\n", a);
  printf("  index = %lu\n", (unsigned long) a->index); // stop warning on cygwin
  printf("  current block = %p\n", a->current_block);
  printf("  free block = %p\n", a->free_block);
  printf("  mark = %p\n", a->top_mark);
}

static arena_t arena;

int main(void) {
  void *tst;

  init_arena(&arena);
  print_arena(&arena);

  tst = arena_alloc(&arena, 11);
  printf("--- Allocated 11 bytes: ptr = %p ---\n", tst);
  print_arena(&arena);

  tst = arena_alloc(&arena, 23);
  printf("--- Allocated 23 bytes: ptr = %p ---\n", tst);
  print_arena(&arena);

  arena_push(&arena);
  printf("--- After setting mark ---\n");
  print_arena(&arena);

  tst = arena_alloc(&arena, 31);
  printf("--- Allocated 31 bytes: ptr = %p ---\n", tst);
  print_arena(&arena);

  tst = arena_alloc(&arena, 10000);
  printf("--- Allocated 10000 bytes: ptr = %p ---\n", tst);
  print_arena(&arena);

  arena_pop(&arena);
  printf("--- After backtracking ---\n");
  print_arena(&arena);

  tst = arena_alloc(&arena, 51);
  printf("--- Allocated 51 bytes: ptr = %p ---\n", tst);
  print_arena(&arena);

  arena_reset(&arena);
  printf("--- After reset ---\n");
  print_arena(&arena);

  tst = arena_alloc(&arena, 11);
  printf("--- Allocated 11 bytes: ptr = %p ---\n", tst);
  print_arena(&arena);

  tst = arena_alloc(&arena, 23);
  printf("--- Allocated 23 bytes: ptr = %p ---\n", tst);
  print_arena(&arena);

  delete_arena(&arena);
  return 0;
}
