/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STACK FOR DEPTH-FIRST EXPLORATION OF NESTED IF-THEN-ELSE TERMS
 */
#include "terms/ite_stack.h"
#include "utils/memalloc.h"

/*
 * Initialization:
 * - the stack is empty
 * - the leaf is NULL_TERM
 * - the arrays have the default size.
 */
void init_ite_stack(ite_stack_t *stack) {
  uint32_t n;

  n = DEF_ITE_STACK_SIZE;
  stack->size = n;
  stack->top = 0;
  stack->leaf = NULL_TERM;
  stack->ite = (composite_term_t **) safe_malloc(n * sizeof(composite_term_t *));
  stack->path = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
}


/*
 * Makes stack 50% bigger
 */
static void extend_ite_stack(ite_stack_t *stack) {
  uint32_t n;

  n = stack->size;
  n += n>>1; // 50%
  assert(n > stack->size);

  if (n > MAX_ITE_STACK_SIZE) {
    out_of_memory();
  }
  stack->size = n;
  stack->ite = (composite_term_t **) safe_realloc(stack->ite, n * sizeof(composite_term_t *));
  stack->path = (uint8_t *) safe_realloc(stack->path, n * sizeof(uint8_t));
}


/*
 * Free memory used by stack
 */
void delete_ite_stack(ite_stack_t *stack) {
  safe_free(stack->ite);
  safe_free(stack->path);
  stack->ite = NULL;
  stack->path = NULL;
}


/*
 * Push a term descriptor d = (ite c t e) on the stack
 * - the path is extended to point to t (so t is the new leaf)
 * - We can't check that d is really an if-then-else descriptor but d must have arity 3
 */
void ite_stack_push(ite_stack_t *stack, composite_term_t *d) {
  uint32_t i;

  assert(d->arity == 3);

  i = stack->top;
  if (i == stack->size) {
    extend_ite_stack(stack);
  }

  assert(i < stack->size);
  stack->ite[i] = d;
  stack->path[i] = 0;
  stack->leaf = d->arg[1];
  stack->top = i+1;
}


/*
 * Move to the next branch
 */
void ite_stack_next_branch(ite_stack_t *stack) {
  uint32_t i;

  i = stack->top;
  while (i > 0) {
    i --;
    if (stack->path[i] == (uint8_t) 0) {
      stack->path[i] = (uint8_t) 1;
      stack->leaf = stack->ite[i]->arg[2]; // else part of the last ite
      stack->top = i+1;
      return;
    }
    assert(stack->path[i] == (uint8_t) 1);
  }

  // all paths have been explored
  stack->top = 0;
  stack->leaf = NULL_TERM;
}
