/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STACK OF POINTER ARRAYS
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/ptr_stack.h"

/*
 * Allocate and initialize a block of size n
 */
static pblock_t *new_pblock(uint32_t n) {
  pblock_t *tmp;

  assert(n >= DEFAULT_PBLOCK_SIZE);

  if (n >= MAX_PBLOCK_SIZE) {
    out_of_memory();
  }

  tmp = (pblock_t *) safe_malloc(sizeof(pblock_t) + n * sizeof(void *));
  tmp->next = NULL;
  tmp->size = n;
  tmp->ptr = 0;

  return tmp;
}

/*
 * Allocate a block of default size (or more)
 */
static pblock_t *alloc_pblock(ptr_stack_t *stack) {
  pblock_t *p;

  p = stack->free;
  if (p != NULL) {
    stack->free = p->next;
  } else {
    p = new_pblock(DEFAULT_PBLOCK_SIZE);
  }
  return p;
}


/*
 * Free block b: add it to the free list
 */
static void free_pblock(ptr_stack_t *stack, pblock_t *b) {
  b->next = stack->free;
  stack->free = b;
}


/*
 * Initialize stack
 */
void init_pstack(ptr_stack_t *stack) {
  pblock_t *empty;

  empty = (pblock_t *) safe_malloc(sizeof(pblock_t));
  empty->next = NULL;
  empty->size = 0;
  empty->ptr = 0;
  stack->current = empty;
  stack->free = NULL;
}


/*
 * Deletion
 */
static void delete_pblock_list(pblock_t *b) {
  pblock_t *next;

  while (b != NULL) {
    next = b->next;
    safe_free(b);
    b = next;
  }
}

void delete_pstack(ptr_stack_t *stack) {
  delete_pblock_list(stack->current);
  delete_pblock_list(stack->free);
  stack->current = NULL;
  stack->free = NULL;
}


/*
 * Allocate an array of n pointers
 */
void **alloc_pstack_array(ptr_stack_t *stack, uint32_t n) {
  pblock_t *b;
  uint32_t p;
  void **a;

  if (n == 0) {
    n = 1; // free_pstack_array does not work if arrays are empty
  }

  b = stack->current;
  p = b->ptr + n;
  if (p > b->size) {
    if (n <= DEFAULT_PBLOCK_SIZE) {
      b = alloc_pblock(stack);
    } else {
      b = new_pblock(n);
    }
    b->next = stack->current;
    stack->current = b;
    p = n;
  }
  assert(b->ptr + n <= b->size);
  a = b->data + b->ptr;
  b->ptr = p;

  return a;
}

/*
 * Free array a
 */
void free_pstack_array(ptr_stack_t *stack, void **a) {
  pblock_t *b;
  uint32_t p;

  b = stack->current;
  assert(b->data <= a && a < b->data + b->size);
  p = a - b->data;
  b->ptr = p;
  if (p == 0) {
    stack->current = b->next;
    free_pblock(stack, b);
  }
}


/*
 * Reset: empty the stack
 */
void reset_pstack(ptr_stack_t *stack) {
  pblock_t *b, *next;

  b = stack->current;
  while (b->size > 0) {
    next = b->next;
    b->ptr = 0;
    free_pblock(stack, b);
    b = next;
  }
  stack->current = b;
}
