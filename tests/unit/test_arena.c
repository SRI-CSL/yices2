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
