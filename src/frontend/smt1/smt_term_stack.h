/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TERM-STACK OPERATIONS TO SUPPORT SMT-LIB 1.2
 */

/*
 * The term_stack data structures and main operations
 * are defined in "term_stack.h". To support the
 * SMT-LIB notation (version 1.2), we redefine the
 * following operations:
 *
 * Yices 2 Version                      SMT 1.2 Version
 *
 * [mk-eq <term> <term> ]            [mk-eq <term> .... <term>]
 * [mk-bv-const <size> <value>]      [mk-bv-const <value> <size>]
 * [mk-bv-rotate <bv> <index>]       [mk-bv-rotate <index> <bv>]
 * [mk-bv-repeat <bv> <index>]       [mk-bv-repeat <index> <bv>]
 * [mk-zero-extend <bv> <number>]    [mk-zero-extend <number> <bv> ]
 * [mk-sign-extend <bv> <number>]    [mk-sign-extend <number> <bv> ]
 *
 * NOTE: older version of SMT-LIB, was using the same convention
 * as Yices for sign-extend. We don't support it.
 */

#ifndef __SMT_TERM_STACK
#define __SMT_TERM_STACK

#include "parser_utils/term_stack2.h"

/*
 * Initialize stack for SMT-LIB 1.2:
 * - initialize the stack then redefines the
 *   operations above
 */
extern void init_smt_tstack(tstack_t *stack);


#endif /* __SMT_TERM_STACK */
