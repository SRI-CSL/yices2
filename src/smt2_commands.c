/*
 * ALL SMT-LIB 2 COMMANDS
 */

#include <stdio.h>
#include <assert.h>

#include "smt2_commands.h"


/*
 * GLOBAL OBJECTS
 */
static FILE *err;     // error/trace output: default = stderr
static FILE *out;     // normal output: default = stdout

static char *logic_name;           // logic: initially NULL
static smt_logic_t logic_code;     // code: set after logic_name is given


/*
 * Syntax error (reported by tstack)
 * - lex = lexer 
 * - expected_token = either an smt2_token or -1
 *
 * lex is as follows: 
 * - current_token(lex) = token that caused the error
 * - current_token_value(lex) = corresponding string
 * - current_token_length(lex) = length of that string
 * - lex->tk_line and lex->tk_column = start of the token in the input
 * - lex->reader.name  = name of the input file (NULL means input is stdin)
 */
void smt2_syntax_error(lexer_t *lex, int32_t expected_token) {
  reader_t *rd;
  smt2_token_t tk;

  tk = current_token(lex);
  rd = &lex->reader;

  if (rd->name != NULL) {
    fprintf(err, "%s: ", rd->name);
  }

  switch (tk) {
  case SMT2_TK_INVALID_STRING:
    fprintf(err, "missing string terminator \" (line %"PRId32", column %"PRId32")\n",
            rd->line, rd->column);
    break;

  case SMT2_TK_INVALID_NUMERAL:
    fprintf(err, "invalid numeral %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    break;

  case SMT2_TK_INVALID_DECIMAL:
    fprintf(err, "invalid decimal %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    break;

  case SMT2_TK_INVALID_HEXADECIMAL:
    fprintf(err, "invalid hexadecimal constant %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    break;

  case SMT2_TK_INVALID_BINARY:
    fprintf(err, "invalid binary constant %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    break;

  case SMT2_TK_INVALID_SYMBOL:
    fprintf(err, "invalid symbol (line %"PRId32", column %"PRId32")\n", 
            lex->tk_line, lex->tk_column);
    break;

  case SMT2_TK_INVALID_KEYWORD:
    fprintf(err, "invalid keyword (line %"PRId32", column %"PRId32")\n",
            lex->tk_line, lex->tk_column);
    break;

  case SMT2_TK_ERROR:
    fprintf(err, "invalid token %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    break;
    
  default:
    if (expected_token >= 0) {
      fprintf(err, "syntax error (line %"PRId32", column %"PRId32"): %s expected\n",
              lex->tk_line, lex->tk_column, smt2_token_to_string(expected_token));
    } else {
      fprintf(err, "syntax error (line %"PRId32", column %"PRId32")\n",
              lex->tk_line, lex->tk_column);
    }
    break;
  }
}


