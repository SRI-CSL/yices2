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
 * SMT2 EXPRESSIONS
 */

/*
 * This stores a valid SMT2 expression as a sequence of tokens
 * so that we can pretty-print the expression later in the same
 * format as it was given (more or less!).
 */

#ifndef __SMT2_EXPRESSIONS_H
#define __SMT2_EXPRESSIONS_H

#include <stdint.h>

#include "frontend/smt2/parenthesized_expr.h"
#include "frontend/smt2/smt2_lexer.h"
#include "io/yices_pp.h"


/*
 * Add an SMT2 token to queue
 * - tk = token code (as defined in smt2_lexer.h)
 * - str = string
 * - len = length of the string
 *
 * - if the token is SMT2_TK_LP: open a scope
 *   (str and len are ignored)
 * - if the token is SMT2_TK_RP: close the current scope
 *   (str and len are ignored)
 * - otherwise add an atomic token:
 *   with key = tk, val = 0, ptr = copy of str
 *
 * If tk corresponds is an error token (e.g., SMT2_TK_INVALID_NUMERAL)
 * or if it's a closing parenthesis with no matching open parenthesis
 * then it's just dropped.
 *
 * TODO: we could check whether str is a predefined symbol
 * or keyword and store the corresponding code in val?
 */
extern void push_smt2_token(etk_queue_t *queue, smt2_token_t tk, const char *str, uint32_t len);



/*
 * Pretty printing:
 * - print the expression that starts at index i of queue
 * - i must be valid token index in queue and it must be
 *   the start of a (sub) expression
 * - if i is atomic, it's printed as is
 * - if i is an open token, then we print the sequence of tokens
 *    '(' .... ')' delimited by 'i' and the matching close token
 */
extern void pp_smt2_expr(yices_pp_t *printer, etk_queue_t *queue, int32_t i);


#endif /* __SMT2_EXPRESSIONS_H */

