/*
 * EXTENSION OF TERM-STACK: SMT-LIB 2 COMMANDS
 */

#ifndef __SMT2_TERM_STACK_H
#define __SMT2_TERM_STACK_H

#include "term_stack2.h"

/*
 * Opcodes include
 * - all top-level commands for SMT-LIB 2
 * - special constructors for indexed sort symbols, 
 *   indexed term symbols, and terms with sorts
 * - constructor for attribute list
 * - processing of term annotations
 */
enum smt2_opcodes {
  SMT2_EXIT = NUM_BASE_OPCODES,         // [exit]
  SMT2_GET_ASSERTIONS,                  // [get-assertions]
  SMT2_GET_ASSIGNMENT,                  // [get-assignment]
  SMT2_GET_PROOF,                       // [get-proof]
  SMT2_GET_UNSAT_CORE,                  // [get-unsat-core]
  SMT2_GET_VALUE,                       // [get-value <term> ... <term> ]
  SMT2_GET_OPTION,                      // [get-option <keyword> ]
  SMT2_GET_INFO,                        // [get-info <keyword> ]
  SMT2_SET_OPTION,                      // [set-option <keyword> ] or [set-option <keyword> <value> ]
  SMT2_SET_INFO,                        // [set-info <keyword> ] or [set-info <keyword> <value> ]
  SMT2_SET_LOGIC,                       // [set-logic <symbol> ]
  SMT2_PUSH,                            // [push <numeral> ]
  SMT2_POP,                             // [pop <numeral> ]
  SMT2_ASSERT,                          // [assert <term> ]
  SMT2_CHECK_SAT,                       // [check-sat ]
  SMT2_DECLARE_SORT,                    // [declare-sort <symbol> <numeral> ]
  SMT2_DEFINE_SORT,                     // [define-sort <symbol> <type-binding> ... <type-binding> <sort> ]
  SMT2_DECLARE_FUN,                     // [declare-fun <symbol> <sort> ... <sort> ]
  SMT2_DEFINE_FUN,                      // [define-fun <symbol> <binding> ... <binding> <sort> <term> ]
  // attributes
  SMT2_MAKE_ATTR_LIST,                  // [make-attr-list <value> .... <value> ]
  SMT2_ADD_ATTRIBUTES,                  // [add-attribute <term> <keyword> <value> ... <keyword> <value>] (<value> may be omitted)
  // sort constructors
  SMT2_INDEXED_SORT,                    // [indexed-sort <symbol> <numeral> ... <numeral> ]
  SMT2_APP_INDEXED_SORT,                // [app-indexed-sort <symbol> <numeral> ... <numeral> <sort> ... <sort>]
  // term constructors
  SMT2_INDEXED_TERM,                    // [indexed-term <symbol> <numeral> ... <numeral> ]
  SMT2_SORTED_TERM,                     // [sorted-term <symbol> <sort> ]
  SMT2_SORTED_INDEXED_TERM,             // [sorted-indexed-term <symbol> <numeral> ... <numeral> <sort> ]
  SMT2_INDEXED_APPLY,                   // [indexed-apply <symbol> <numeral> ... <numeral> <term> ... <term>]
  SMT2_SORTED_APPLY,                    // [sorted-apply <symbol> <sort> <term> ... <term> ]
  SMT2_SORTED_INDEXED_APPLY,            // [sorted-indexed-apply <symbol> <numeral> ... <numeral> <sort> <term> ... <term> ]
} smt2_opcodes_t;

#define NUM_SMT2_OPCODES (SMT2_SORTED_INDEXED_APPLY+1)

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
// symbol in indexed sorts (currently that's only (_ BitVec <n>))
extern void tstack_push_idx_sort(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

// symbol in indexed sort constructor (don't exist in any theory yet)
extern void tstack_push_idx_sort_constructor(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

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
 */
extern void init_smt2_tstack(tstack_t *stack);


#endif /* __SMT2_TERM_STACK_H */
