/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Token sequence and pretty printing of SMT2 expressions.
 */

#include "frontend/smt2/smt2_expressions.h"

/*
 * Add an SMT2 token to queue
 * - tk = token code (as defined in smt2_lexer.h)
 * - str = string
 * - len = length of the string
 *
 * - if the token is SMT2_TK_LP: open a scope
 * - if the token is SMT2_TK_RP: close the current scope
 * - otherwise add an atomic token:
 *   with key = tk, val = 0, ptr = copy of str
 *
 * TODO: we could check whether str is a predefined symbol
 * or keyword and store the corresponding code in val?
 */
void push_smt2_token(etk_queue_t *queue, smt2_token_t tk, const char *str, uint32_t len) {
  switch (tk) {
  case SMT2_TK_LP:
    etk_queue_open_scope(queue);
    break;

  case SMT2_TK_RP:
    if (etk_queue_is_open(queue)) {
      etk_queue_close_scope(queue);
    }
    // otherwise just drop the token
    break;

  case SMT2_TK_EOS: // skip it: can't print anything
    break;

  case SMT2_TK_NUMERAL:
  case SMT2_TK_DECIMAL:
  case SMT2_TK_HEXADECIMAL:
  case SMT2_TK_BINARY:
  case SMT2_TK_STRING:
  case SMT2_TK_SYMBOL:
  case SMT2_TK_QSYMBOL: // same as TK_SYMBOL but within | .. |
  case SMT2_TK_KEYWORD:
  case SMT2_TK_PAR:
  case SMT2_TK_NUM:
  case SMT2_TK_DEC:
  case SMT2_TK_STR:
  case SMT2_TK_UNDERSCORE:
  case SMT2_TK_BANG:
  case SMT2_TK_AS:
  case SMT2_TK_LET:
  case SMT2_TK_EXISTS:
  case SMT2_TK_FORALL:
  case SMT2_TK_ASSERT:
  case SMT2_TK_CHECK_SAT:
  case SMT2_TK_DECLARE_SORT:
  case SMT2_TK_DECLARE_FUN:
  case SMT2_TK_DEFINE_SORT:
  case SMT2_TK_DEFINE_FUN:
  case SMT2_TK_EXIT:
  case SMT2_TK_GET_ASSERTIONS:
  case SMT2_TK_GET_ASSIGNMENT:
  case SMT2_TK_GET_INFO:
  case SMT2_TK_GET_OPTION:
  case SMT2_TK_GET_PROOF:
  case SMT2_TK_GET_UNSAT_CORE:
  case SMT2_TK_GET_VALUE:
  case SMT2_TK_POP:
  case SMT2_TK_PUSH:
  case SMT2_TK_SET_LOGIC:
  case SMT2_TK_SET_INFO:
  case SMT2_TK_SET_OPTION:
  case SMT2_TK_GET_MODEL:
  case SMT2_TK_ECHO:
  case SMT2_TK_RESET:
    etk_queue_push_token(queue, tk, 0, str, len);
    break;

  case SMT2_TK_INVALID_STRING:
  case SMT2_TK_INVALID_NUMERAL:
  case SMT2_TK_INVALID_DECIMAL:
  case SMT2_TK_INVALID_HEXADECIMAL:
  case SMT2_TK_INVALID_BINARY:
  case SMT2_TK_INVALID_SYMBOL:
  case SMT2_TK_INVALID_KEYWORD:
  case SMT2_TK_ERROR:
    // skip all error tokens
    break;
  }
}


/*
 * Pretty printing: send token to the pretty printer
 */
static void pp_smt2_token(yices_pp_t *printer, etoken_t *token) {
  switch (token->key) {
  case ETK_OPEN:
    pp_open_block(printer, PP_OPEN_PAR);
    break;

  case ETK_CLOSE:
    pp_close_block(printer, true);
    break;

  case SMT2_TK_QSYMBOL: // same as TK_SYMBOL but within | .. |
    pp_qstring(printer, '|', '|', token->ptr);
    break;

  case SMT2_TK_STRING:
    pp_qstring(printer, '"', '"', token->ptr);
    break;

  case SMT2_TK_NUMERAL:
  case SMT2_TK_DECIMAL:
  case SMT2_TK_HEXADECIMAL:
  case SMT2_TK_BINARY:
  case SMT2_TK_SYMBOL:
  case SMT2_TK_KEYWORD:
  case SMT2_TK_PAR:
  case SMT2_TK_NUM:
  case SMT2_TK_DEC:
  case SMT2_TK_STR:
  case SMT2_TK_UNDERSCORE:
  case SMT2_TK_BANG:
  case SMT2_TK_AS:
  case SMT2_TK_LET:
  case SMT2_TK_EXISTS:
  case SMT2_TK_FORALL:
  case SMT2_TK_ASSERT:
  case SMT2_TK_CHECK_SAT:
  case SMT2_TK_DECLARE_SORT:
  case SMT2_TK_DECLARE_FUN:
  case SMT2_TK_DEFINE_SORT:
  case SMT2_TK_DEFINE_FUN:
  case SMT2_TK_EXIT:
  case SMT2_TK_GET_ASSERTIONS:
  case SMT2_TK_GET_ASSIGNMENT:
  case SMT2_TK_GET_INFO:
  case SMT2_TK_GET_OPTION:
  case SMT2_TK_GET_PROOF:
  case SMT2_TK_GET_UNSAT_CORE:
  case SMT2_TK_GET_VALUE:
  case SMT2_TK_POP:
  case SMT2_TK_PUSH:
  case SMT2_TK_SET_LOGIC:
  case SMT2_TK_SET_INFO:
  case SMT2_TK_SET_OPTION:
  case SMT2_TK_GET_MODEL:
  case SMT2_TK_ECHO:
  case SMT2_TK_RESET:
    pp_string(printer, token->ptr);
    break;

  default:
    assert(false);
    break;
  }
}


/*
 * Pretty printing:
 * - print the expression that starts at index i of queue
 * - i must be valid token index in queue and it must be
 *   the start of a (sub) expression
 * - if i is atomic, it's printed as is
 * - if i is an open token, then we print the sequence of tokens
 *    '(' .... ')' delimited by 'i' and the matching close token
 */
void pp_smt2_expr(yices_pp_t *printer, etk_queue_t *queue, int32_t i) {
  int32_t n;

  n = token_sibling(queue, i);
  while (i < n) {
    pp_smt2_token(printer, get_etoken(queue, i));
    i++;
  }
}
