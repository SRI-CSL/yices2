/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STACK FOR DEPTH-FIRST EXPLORATION OF NESTED IF-THEN-ELSE TERMS
 */

/*
 * We store a stack of composite_terms. Each of them is an if-then-else
 * descriptor (so it has arity three). We also stoe a path = a stack of 
 * 0 or 1 integers.
 *
 * This represents nested if-then-elses as follows:
 * - bottom element = (ite c0 t0 e0)
 *   first path value = either 0 or 1
 *   if the value is 0, then the next element on the stack is the
 *   if-then-else descriptor of t0, otherwise, it's the descriptor of e0.
 * - next element = (ite c1 t1 e1) 
 *   path value = either 0 or 1
 *
 * Thus, we can see this as a tree of if-then-else nodes with root
 * (ite c0 t0 e0).  The path defines a branch in this tree and we
 * provide operation to get the current leaf (last term on the branch)
 * and move to the next branch.
 */

#ifndef __ITE_STACK_H
#define __ITE_STACK_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/terms.h"


/*
 * Stack:
 * - two arrays of the same size to store descriptors + path.
 * - leaf is the current leaf term or NULL_TERM if the stack is empty
 */
typedef struct ite_stack_s {
  uint32_t size;           // size of the two arrays
  uint32_t top;            // top of the stack
  term_t leaf;             // current leaf term (NU
  composite_term_t **ite;  // array of descriptors
  uint8_t *path;           // array of 0/1 values
} ite_stack_t;

#define DEF_ITE_STACK_SIZE 20
#define MAX_ITE_STACK_SIZE (UINT32_MAX/sizeof(composite_term_t *))


/*
 * Initialization:
 * - the stack is empty
 * - the leaf is NULL_TERM
 * - the arrays have the default size.
 */
extern void init_ite_stack(ite_stack_t *stack);

/*
 * Reset: empty the stack
 */
static inline void reset_ite_stack(ite_stack_t *stack) {
  stack->top = 0;
  stack->leaf = NULL_TERM;
}

/*
 * Free memory used
 */
extern void delete_ite_stack(ite_stack_t *stack);

/*
 * Push a term descriptor d = (ite c t e) on the stack
 * - the path is extended to point to t (so t is the new leaf)
 * - We can't check that d is really an if-then-else descriptor but d must have arity 3
 */
extern void ite_stack_push(ite_stack_t *stack, composite_term_t *d);

/*
 * Check emptiness
 */
static inline bool ite_stack_is_empty(ite_stack_t *stack) {
  return stack->top == 0;
}

static inline bool ite_stack_is_nonempty(ite_stack_t *stack) {
  return stack->top > 0;
}


/*
 * Depth/path length = number of elements on the stack
 */
static inline uint32_t ite_stack_depth(ite_stack_t *stack) {
  return stack->top;
}


/*
 * Update the stack to move to the next branch
 * - this pops all elements that have been fully explored
 *   (i.e., if the path is of the form ...0111...11, then
 *   the 111...11 suffix is removed and the preceding 0 is
 *   flipped to 1)
 * - the leaf is updated
 * - the stack may become empty as a result of this operation.
 */
extern void ite_stack_next_branch(ite_stack_t *stack);



#endif /* __ITE_STACK_H */
