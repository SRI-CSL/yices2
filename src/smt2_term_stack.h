/*
 * EXTENSION OF TERM-STACK: SMT-LIB 2 COMMANDS
 */

#ifndef __SMT2_TERM_STACK_H
#define __SMT2_TERM_STACK_H

#include "term_stack2.h"

/*
 * Special treatment of function and sort symbols
 * - the following function take a symbol argument
 * - they check whether the symbol is a built-in SMT2 symbol for 
 *   the current logic
 * - if so they convert the symbol to a built-in operation
 * - if the symbol is not built-in, then a generic form of the
 *   operation is pushed on the stack
 *
 * Example;
 * - tstack_push_smt2_op(tstack, "OR", 2, loc) is treated as 
 *      push_op(mk_or, ...)
 * - tstack_push_smt2_op(tstack, "f", 1, loc) is treated as 
 *      push_op(mk_apply, ...); 
 *      push_term_by_name("f",,,,)
 */

// symbol as a sort name (e.g., Int)
extern void tstack_push_sort_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

// symbol in indexed sorts (currently that's only (_ BitVec <n>))
extern void tstack_push_idx_sort(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

// symbol as a sort constructor: (e.g. Array)
extern void tstack_push_sort_constructor(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

// symbol in indexed sort constructor (don't exist in any theory yet)
extern void tstack_push_idx_sort_constructor(tstack_t *stack, char *s, uint32_t n, loc_t *loc);


// symbol as a term name
extern void tstack_push_term_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

// symbol in function application
extern void tstack_push_smt2_op(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

// symbol in indexed function application
extern void tstack_push_smt2_idx_op(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

// symbol in indexed term
extern void tstack_push_idx_term(tstack_t *stack, char *s, uint32_t n, loc_t *loc);


/*
 * Initialize stack for SMT2:
 * - add all the operations defined above
 * - modify the implementation of default operations
 * - this must be called after init_smt2() because it needs __smt2_globals.avtbl
 */
extern void init_smt2_tstack(tstack_t *stack);


#endif /* __SMT2_TERM_STACK_H */
