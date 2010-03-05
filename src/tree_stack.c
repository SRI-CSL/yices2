/*
 * STACK FOR PROCESSING TERMS/FORMULAS
 */

#include "memalloc.h"
#include "tree_stack.h"


/*
 * Initialization:
 * - n = size 
 * - if n = 0 the default size is used
 */
void init_tree_stack(tree_stack_t *stack, uint32_t n) {
  tree_record_t *tmp;

  if (n == 0) {
    n = TREE_STACK_DEFAULT_SIZE;
  }
  if (n > TREE_STACK_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (tree_record_t *) safe_malloc(n * sizeof(tree_record_t));
  stack->data = tmp;
  stack->top_ptr = tmp - 1; // we maintain the invariant top_ptr == data + (top - 1)
  stack->size = n;
  stack->top = 0;
}

/*
 * Deletion
 */
void delete_tree_stack(tree_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Extend the data array by 50%
 */
void extend_tree_stack(tree_stack_t *stack) {
  uint32_t n;
  tree_record_t *tmp;

  n = stack->size + 1;
  n += n>>1;

  if (n > TREE_STACK_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (tree_record_t *) safe_realloc(stack->data, n * sizeof(tree_record_t));
  stack->data = tmp;
  stack->top_ptr = (tmp - 1) + stack->top;
  stack->size = n;
}

