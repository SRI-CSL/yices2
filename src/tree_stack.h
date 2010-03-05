/*
 * STACK FOR PROCESSING TERMS/FORMULAS
 */

/*
 * Because terms and formulas can be very deep, using ordinary
 * recursive functions can lead to stack overflows.
 * This is an annoying problem because
 * 1) on many systems, there's no visible difference between 
 *    stack overflow and segmentation fault. So people think
 *    there's a bug when stack overflow occurs.
 * 2) on some systems (cygwin, mingw) there's no way for the user to 
 *    increase the stack size (setlimit does not work).
 *
 * So it's safer to use our own stack when processing/visiting terms.
 */

#ifndef __TREE_STACK_H
#define __TREE_STACK_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "terms.h"

/*
 * Stack structure:
 * - each stack element includes: 
 *   term id, kind, type, descriptor
 * + a counter (number of children already visited)
 */
typedef struct tree_record_s {
  term_t term; // id
  type_t type;
  term_kind_t kind;
  int32_t counter; 
  term_desc_t desc;
} tree_record_t;

typedef struct tree_stack_s {
  tree_record_t *data;
  tree_record_t *top_ptr; // pointer to top record 
  uint32_t size; // of data array
  uint32_t top;  // index in data array
} tree_stack_t;
  

/*
 * Default and max size
 */
#define TREE_STACK_DEFAULT_SIZE 100
#define TREE_STACK_MAX_SIZE (UINT32_MAX/sizeof(tree_record_t))

/*
 * Initialization:
 * - n = size 
 * - if n = 0 the default size is used
 */
extern void init_tree_stack(tree_stack_t *stack, uint32_t n);

/*
 * Deletion
 */
extern void delete_tree_stack(tree_stack_t *stack);


/*
 * Extend the data array by 50%
 */
extern void extend_tree_stack(tree_stack_t *stack);


/*
 * Check whether the stack is empty
 */
static inline bool tree_stack_empty(tree_stack_t *stack) {
  return stack->top == 0;
}

static inline bool tree_stack_nonempty(tree_stack_t *stack) {
  return stack->top > 0;
}

/*
 * Get top pointer
 */
static inline tree_record_t *tree_stack_top(tree_stack_t *stack) {
  assert(tree_stack_nonempty(stack));
  return stack->top_ptr;
}

/*
 * Pop top record (top_ptr becomes invalid if the stack this empties
 * the stack).
 */
static inline void tree_stack_pop(tree_stack_t *stack) {
  assert(tree_stack_nonempty(stack));
  stack->top --;
  stack->top_ptr --;
}


/*
 * Push an uninitialized record
 */
static inline void tree_stack_push(tree_stack_t *stack) {
  uint32_t i;

  i = stack->top;
  if (i >= stack->size) {
    extend_tree_stack(stack);
  }
  stack->top ++;
  stack->top_ptr ++;
  assert(stack->top_ptr == stack->data + (stack->top - 1));
}


/*
 * Push term t: components are extracted from the given term table.
 * - counter is set to 0
 */
static inline void tree_stack_push_term(tree_stack_t *stack, term_table_t *tbl, term_t t) {
  tree_record_t *r;

  tree_stack_push(stack);
  r = stack->top_ptr;
  r->term = t;
  r->type = term_type(tbl, t);
  r->kind = term_kind(tbl, t);
  r->counter = 0;
  r->desc = tbl->desc[t];
}


/*
 * Empty the stack
 */
static inline void tree_stack_reset(tree_stack_t *stack) {
  stack->top = 0;
  stack->top_ptr = stack->data  - 1;
}

#endif /* __TREE_STACK_H */

