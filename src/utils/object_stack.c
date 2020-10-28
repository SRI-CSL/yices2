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
 * STACK OF OBJECTS WITH SUPPORT FOR CLEANUP
 */

#include <assert.h>
#include <stdbool.h>

#include "utils/memalloc.h"
#include "utils/object_stack.h"



/*
 * For debugging: check alignment
 */
#ifndef NDEBUG
static bool size_is_multiple_of_sixteen(size_t s) {
  return (s & ((size_t) 15)) == 0;
}
#endif

/*
 * Round n to the next multiple of 16
 */
static inline size_t round_up_size(size_t s) {
  return ((s + 15) >> 4) << 4;
}

/*
 * Size for the metada
 */
#define OBJSTACK_META_SIZE round_up_size(sizeof(objstack_meta_t))


/*
 * Start address of object defined by m
 */
static inline void *obj(objstack_meta_t *m) {
  return (void*) (((char *) m) + OBJSTACK_META_SIZE);
}

/*
 * Initialize the stack. Nothing is allocated yet.
 */
void init_objstack(objstack_t *stack) {
  stack->current = NULL;
  stack->available = 0;
  stack->free = NULL;
}

/*
 * Get a block: either the first element in the free list
 * or a newly allocated block if the free list is empty.
 */
static objstack_block_t *get_block(objstack_t *stack) {
  objstack_block_t *b;

  b = stack->free;
  if (b != NULL) {
    stack->free = b->h.next;
  } else {
    b = safe_malloc(sizeof(objstack_block_t));
  }
  return b;
}

/*
 * Free block b: add it to the free list
 */
static void free_block(objstack_t *stack, objstack_block_t *b) {
  b->h.next = stack->free;
  stack->free = b;
}


/*
 * Make room for n bytes in the stack:
 * - take them from the current block if there's enough room
 * - close the current block and add a new block otherwise.
 * - n must be positive and less than BLOCK_SIZE
 */
static void objstack_alloc_bytes(objstack_t *stack, size_t n) {
  objstack_block_t *b;

  assert(n > 0 && n <= OBJSTACK_BLOCK_SIZE && size_is_multiple_of_sixteen(n));

  if (n > stack->available) {
    // close the current block 
    if (stack->current != NULL) {
      stack->current->h.leftover = stack->available;
    }
    // get a new block
    b = get_block(stack);
    b->h.next = stack->current;
    stack->available = OBJSTACK_BLOCK_SIZE;
    stack->current = b;
  }
  assert(n <= stack->available);
  stack->available -= n;
}

/*
 * Pointer to the first object in the stack (i.e., the one that was allocated
 * most recently).
 */
static inline objstack_meta_t *objstack_first(objstack_t *stack) {
  assert(stack->current != NULL);
  return (objstack_meta_t *) (stack->current->data + stack->available);
}


/*
 * Pop the current block
 */
static void pop_current_block(objstack_t *stack) {
  objstack_block_t *b;

  assert(stack->current != NULL);

  b = stack->current;
  stack->current = b->h.next;
  if (b->h.next != NULL) {
    stack->available = b->h.next->h.leftover;
  } else {
    stack->available = 0;
  }
  free_block(stack, b);
}



/*
 * Allocate an object of size n
 * - n must be no more than MAX_OBJSTACK_SIZE
 * - f = the cleaner function for this object (or NULL if no cleaner needed).
 */
void *objstack_alloc(objstack_t *stack, size_t n, cleaner_t f) {
  objstack_meta_t *m;

  assert(n <= MAX_OBJSTACK_SIZE);

  n = round_up_size(n);
  objstack_alloc_bytes(stack, n + OBJSTACK_META_SIZE);
  m = objstack_first(stack);
  m->size = n;
  m->cleaner = f;
  return obj(m);
}


/*
 * Cleanup and free the last allocated object
 */
void objstack_pop(objstack_t *stack) {
  objstack_meta_t *m;

  if (stack->available == OBJSTACK_BLOCK_SIZE) {
    // the current block is empty
    pop_current_block(stack);
  }
  assert(stack->current != NULL);
  m = objstack_first(stack);
  if (m->cleaner != NULL) {
    m->cleaner(obj(m));
  }
  stack->available += m->size + OBJSTACK_META_SIZE;
}


/*
 * Cleanup all the objects in block b
 */
static void cleanup_objects(objstack_block_t *b) {
  objstack_meta_t *m;
  size_t i;

  i = b->h.leftover;
  assert(i <= OBJSTACK_BLOCK_SIZE);

  while (i < OBJSTACK_BLOCK_SIZE) {
    m = (objstack_meta_t *) (b->data + i);
    if (m->cleaner != NULL) {
      m->cleaner(obj(m));
    }
    i += m->size + OBJSTACK_META_SIZE;
  }
}

/*
 * Reset: call the cleaner function on all allocated objects
 * then empty the stack.
 */
void reset_objstack(objstack_t *stack) {
  objstack_block_t *b, *n;

  if (stack->current != NULL) {
    b = stack->current;
    b->h.leftover = stack->available;
    do {
      cleanup_objects(b);
      n = b->h.next;
      free_block(stack, b);
      b = n;
    } while (b != NULL);

    stack->current = NULL;
    stack->available = 0;
  }
}

/*
 * Delete: reset then delete all blocks in the free list
 */
void delete_objstack(objstack_t *stack) {
  objstack_block_t *b, *n;

  reset_objstack(stack);
  b = stack->free;
  while (b != NULL) {
    n = b->h.next;
    safe_free(b);
    b = n;
  }
  stack->free = NULL;
}


