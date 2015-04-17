/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STACK OF INTEGERS/INTEGER ARRAYS
 */

#include <assert.h>

#include "utils/int_stack.h"
#include "utils/memalloc.h"

/*
 * Allocate and initialize a block of size n
 */
static iblock_t *new_iblock(uint32_t n) {
  iblock_t *tmp;

  assert(n >= DEFAULT_IBLOCK_SIZE);

  if (n >= MAX_IBLOCK_SIZE) {
    out_of_memory();
  }

  tmp = (iblock_t *) safe_malloc(sizeof(iblock_t) + n * sizeof(int32_t));
  tmp->next = NULL;
  tmp->size = n;
  tmp->ptr = 0;

  return tmp;
}

/*
 * Allocate a block of default size (or more)
 */
static iblock_t *alloc_iblock(int_stack_t *stack) {
  iblock_t *p;

  p = stack->free;
  if (p != NULL) {
    stack->free = p->next;
  } else {
    p = new_iblock(DEFAULT_IBLOCK_SIZE);
  }
  return p;
}


/*
 * Free block b: add it to the free list
 */
static void free_iblock(int_stack_t *stack, iblock_t *b) {
  b->next = stack->free;
  stack->free = b;
}


/*
 * Initialize stack
 */
void init_istack(int_stack_t *stack) {
  iblock_t *empty;

  empty = (iblock_t *) safe_malloc(sizeof(iblock_t));
  empty->next = NULL;
  empty->size = 0;
  empty->ptr = 0;
  stack->current = empty;
  stack->free = NULL;
}


/*
 * Deletion
 */
static void delete_iblock_list(iblock_t *b) {
  iblock_t *next;

  while (b != NULL) {
    next = b->next;
    safe_free(b);
    b = next;
  }
}

void delete_istack(int_stack_t *stack) {
  delete_iblock_list(stack->current);
  delete_iblock_list(stack->free);
  stack->current = NULL;
  stack->free = NULL;
}


/*
 * Allocate an array of n integers
 */
int32_t *alloc_istack_array(int_stack_t *stack, uint32_t n) {
  iblock_t *b;
  uint32_t p;
  int32_t *a;

  if (n == 0) {
    n = 1; // free_istack_array does not work if arrays are empty
  }

  b = stack->current;
  p = b->ptr + n;
  if (p > b->size) {
    if (n <= DEFAULT_IBLOCK_SIZE) {
      b = alloc_iblock(stack);
    } else {
      b = new_iblock(n);
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
void free_istack_array(int_stack_t *stack, int32_t *a) {
  iblock_t *b;
  uint32_t p;

  b = stack->current;
  assert(b->data <= a && a < b->data + b->size);
  p = a - b->data;
  b->ptr = p;
  if (p == 0) {
    stack->current = b->next;
    free_iblock(stack, b);
  }
}


/*
 * Reset: empty the stack
 */
void reset_istack(int_stack_t *stack) {
  iblock_t *b, *next;

  b = stack->current;
  while (b->size > 0) {
    next = b->next;
    b->ptr = 0;
    free_iblock(stack, b);
    b = next;
  }
  stack->current = b;
}
