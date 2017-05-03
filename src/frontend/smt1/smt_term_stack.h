/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
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
