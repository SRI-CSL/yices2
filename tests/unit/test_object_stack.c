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

/*
 * Test object stack
 */

#include <assert.h>
#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>

#include "utils/object_stack.h"


#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif


/*
 * Round s to the next multiple of 16
 */
static inline size_t round_up(size_t s) {
  return ((s + 15) >> 4) << 4;
}


/*
 * Print objects in block b
 * - i = index for numbering
 * - s = start of objects in b.
 * return i + the number of objects in the block.
 */
static uint32_t print_block(FILE *f, objstack_block_t *b, uint32_t i,  size_t s) {
  objstack_meta_t *m;
  char *o;

  fprintf(f, "  block %p\n", b);
  while (s < OBJSTACK_BLOCK_SIZE) {    
    m = (objstack_meta_t *) (b->data + s);
    o = b->data + (s + round_up(sizeof(objstack_meta_t)));

    fprintf(f, "    obj[%"PRIu32"]: size = %zu, cleaner = %p, addr = %p\n", i, m->size, m->cleaner, o);
    assert(o + m->size <= b->data + OBJSTACK_BLOCK_SIZE);

    s += m->size + round_up(sizeof(objstack_meta_t));
    i ++;
  }

  return i;
}

static void print_stack(FILE *f, objstack_t *stack) {
  objstack_block_t *b;
  size_t s;
  uint32_t i;

  fprintf(f, "stack %p\n", stack);
  fprintf(f, "  current = %p\n", stack->current);
  fprintf(f, "  available = %zu\n", stack->available);
  fprintf(f, "  free = %p\n", stack->free);

  i = 0;
  b = stack->current;
  s = stack->available;
  while (b != NULL) {
    i = print_block(f, b, i, s);
    b = b->h.next;
    if (b != NULL) s = b->h.leftover;
  }

  if (i == 0) {
    fprintf(f, "  empty stack\n");
  }
}

static void test1(void) {
  objstack_t stack;

  printf("\n=== test1 ===\n\n");
  init_objstack(&stack); 
  printf("initial stack\n");
  print_stack(stdout, &stack);

  objstack_alloc(&stack, 10, NULL);
  objstack_alloc(&stack, 1000, NULL);
  printf("\nafter two allocs\n");
  print_stack(stdout, &stack);

  objstack_pop(&stack);
  printf("\nafter pop\n");
  print_stack(stdout, &stack);

  objstack_alloc(&stack, MAX_OBJSTACK_SIZE, NULL);
  objstack_alloc(&stack, 2000, NULL);
  printf("\nafter max alloc\n");
  print_stack(stdout, &stack);

  objstack_pop(&stack);
  objstack_pop(&stack);
  objstack_pop(&stack);
  printf("\nafter three pops\n");
  print_stack(stdout, &stack);

  reset_objstack(&stack);
  printf("\nafter reset\n");
  print_stack(stdout, &stack);

  delete_objstack(&stack);
  printf("\nafter delete\n");
  print_stack(stdout, &stack);
}



/*
 * Some data structure for testing:
 * - an
 */
typedef struct test_obj_s {
  uint32_t id;
} test_obj_t;

static void cleaner(void *o) {
  printf("  deleting obj %"PRIu32" at addr %p\n", ((test_obj_t *) o)->id, o);
}

// random size between 4 and MAX_OBJSTACK_SIZE
static size_t random_size(void) {
  uint32_t x = random() % 10;
  size_t s;

  if (x == 9) {
    s = MAX_OBJSTACK_SIZE;
  } else {
    s = sizeof(uint32_t) + (size_t) (10 * x);
  }

  assert(4 <= s && s <= MAX_OBJSTACK_SIZE);

  return s;
}

static void alloc(objstack_t *stack, uint32_t id) {
  test_obj_t *o;
  size_t s;

  s = random_size();
  o = objstack_alloc(stack, s, cleaner);
  o->id = id;

  printf("  allocating obj %"PRIu32": size = %zu, addr = %p\n", id, s, o);
}

static void test2(void) {
  objstack_t stack;
  uint32_t depth, rnd, i, n;

  printf("\n=== test2 ===\n\n");
  
  init_objstack(&stack);
  n = 1000; // number of random operations
  depth = 0;
  for (i=0; i<n; i++) {
    rnd = random() % 20;
    if (rnd == 0) {
      printf("reset\n");
      reset_objstack(&stack);
      depth = 0;
    } else if (rnd <= 10) {
      printf("push\n");
      alloc(&stack, depth);
      depth ++;
    } else if (depth > 0) {
      printf("pop\n");
      objstack_pop(&stack);
      depth --;
    }

    if (i % 100 == 99) {
      printf("\nAfter %"PRIu32" operations\n", i+1);
      print_stack(stdout, &stack);
    }
  }

  reset_objstack(&stack);
  delete_objstack(&stack);
}


int main(void) {
  test1();
  test2();

  return 0;
}
