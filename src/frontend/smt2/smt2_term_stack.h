/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * EXTENSION OF TERM-STACK: SMT-LIB 2 COMMANDS
 */

#ifndef __SMT2_TERM_STACK_H
#define __SMT2_TERM_STACK_H

#include "parser_utils/term_stack2.h"

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
 * More symbol processing for qualified expressions:
 *  SORTED_TERM:          (as <symbol> <sort>)
 *  SORTED_INDEXED_TERM   (as (_ <symbol> <idx> ... <idx>) <sort> )
 *  SORTED_APPLY:         ((as <symbol> <sort>) <arg> ... <arg> )
 *  SORTED_INDEXED_APPLY  ((as (_ <symbol> <idx> ... <idx>) <sort> ) <arg> .... <arg>)
 *
 * In these expressions, we check whether <symbol> is defined and maps to
 * one operation. If so, we push the operation's opcode onto the stack.
 */

// term name in SORTED_TERM
extern void tstack_push_qual_term_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

// indexed term name in SORTED_INDEXED_TERM
extern void tstack_push_qual_idx_term_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

// function name in SORTED_APPLY
extern void tstack_push_qual_smt2_op(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

// function name in SORTED_INDEXED_APPLY
extern void tstack_push_qual_smt2_idx_op(tstack_t *stack, char *s, uint32_t n, loc_t *loc);


/*
 * More for sort names/function names in declarations/definitions:
 *    (define-sort  <symbol> ...)
 *    (declare-sort <symbol> ...)
 *    (define-fun   <symbol> ...)
 *    (declare-fun  <symbol> ...)
 */
// symbol in a sort declaration/definition
extern void tstack_push_free_sort_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

// symbol in a function declaration/definition
extern void tstack_push_free_fun_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc);


/*
 * Initialize stack for SMT2:
 * - add all the operations defined above
 * - modify the implementation of default operations
 * - this must be called after init_smt2() because it needs __smt2_globals.avtbl
 */
extern void init_smt2_tstack(tstack_t *stack);


#endif /* __SMT2_TERM_STACK_H */
