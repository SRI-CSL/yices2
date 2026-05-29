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
 * Parser for the Yices language.
 */

#include <stdio.h>
#include <setjmp.h>
#include <inttypes.h>

#include "api/yices_globals.h"
#include "frontend/yices/yices_lexer.h"
#include "frontend/yices/yices_parse_tables.h"
#include "frontend/yices/yices_parser.h"
#include "frontend/yices/yices_tstack_ops.h"
#include "parser_utils/term_stack_error.h"

//IAM: FIXME:
extern error_report_t *yices_error_report(void);

/*
 * Short cuts to save typing
 */
static inline char *tkval(lexer_t *lex) {
  return current_token_value(lex);
}

static inline uint32_t tklen(lexer_t *lex) {
  return current_token_length(lex);
}


/*
 * Name of the current input file (NULL if stdin)
 */
static inline const char *reader_name(lexer_t *lex) {
  return lex->reader.name;
}


/*
 * Store error code and location data for a syntax error
 * - lex = lexer
 * - expected_token = what was expected
 */
static void export_syntax_error(lexer_t *lex, int32_t expected_token) {
  error_report_t *error;
  reader_t *rd;
  yices_token_t tk;

  error = yices_error_report(); //IAM: __yices_globals.error;
  rd = &lex->reader;
  tk = current_token(lex);
  switch (tk) {
  case TK_OPEN_STRING:
    error->code = INVALID_TOKEN;
    error->line = rd->line;
    error->column = rd->column;
    break;

  case TK_EMPTY_BVCONST:
    error->code = INVALID_BVBIN_FORMAT;
    error->line = lex->tk_line;
    error->column = lex->tk_column;
    break;

  case TK_EMPTY_HEXCONST:
    error->code = INVALID_BVHEX_FORMAT;
    error->line = lex->tk_line;
    error->column = lex->tk_column;
    break;

  case TK_INVALID_NUM:
    error->code = INVALID_TOKEN; // invalid rational or float
    error->line = lex->tk_line;
    error->column = lex->tk_column;
    break;

  case TK_ZERO_DIVISOR:
    error->code = DIVISION_BY_ZERO;
    error->line = lex->tk_line;
    error->column = lex->tk_column;
    break;

  case TK_ERROR:
    error->code = INVALID_TOKEN;
    error->line = lex->tk_line;
    error->column = lex->tk_column;
    break;

  default:
    error->code = SYNTAX_ERROR;
    error->line = lex->tk_line;
    error->column = lex->tk_column;
    break;
  }
}


/*
 * Table for conversion of tstack error codes to yices error codes
 * (YICES_NO_ERROR means a bug)
 */
static error_code_t const tstack_error2yices_error[NUM_TSTACK_ERRORS] = {
  YICES_NO_ERROR,                     //  TSTACK_NO_ERROR
  YICES_NO_ERROR,                     //  TSTACK_INTERNAL_ERROR
  YICES_NO_ERROR,                     //  TSTACK_OP_NOT_IMPLEMENTED
  UNDEFINED_TERM_NAME,          //  TSTACK_UNDEF_TERM
  UNDEFINED_TYPE_NAME,          //  TSTACK_UNDEF_TYPE
  YICES_NO_ERROR,                     //  TSTACK_UNDEF_MACRO  // TODO find proper code
  INVALID_RATIONAL_FORMAT,      //  TSTACK_RATIONAL_FORMAT
  INVALID_FLOAT_FORMAT,         //  TSTACK_FLOAT_FORMAT
  INVALID_BVBIN_FORMAT,         //  TSTACK_BVBIN_FORMAT
  INVALID_BVHEX_FORMAT,         //  TSTACK_BVHEX_FORMAT
  REDEFINED_TYPE_NAME,          //  TSTACK_TYPENAME_REDEF
  REDEFINED_TERM_NAME,          //  TSTACK_TERMNAME_REDEF
  YICES_NO_ERROR,                     //  TSTACK_MACRO_REDEF  // TODO find proper code
  DUPLICATE_NAME_IN_SCALAR,     //  TSTACK_DUPLICATE_SCALAR_NAME
  DUPLICATE_VAR_NAME,           //  TSTACK_DUPLICATE_VAR_NAME
  YICES_NO_ERROR,                     //  TSTACK_DUPLICATE_TYPE_VAR_NAME  // TODO find proper code
  YICES_NO_ERROR,                     //  TSTACK_INVALID_OP
  WRONG_NUMBER_OF_ARGUMENTS,    //  TSTACK_INVALID_FRAME
  INTEGER_OVERFLOW,             //  TSTACK_INTEGER_OVERFLOW
  NONNEG_INT_REQUIRED,          //  TSTACK_NEGATIVE_EXPONENT
  INTEGER_REQUIRED,             //  TSTACK_NOT_AN_INTEGER
  YICES_NO_ERROR,                     //  TSTACK_NOT_A_STRING  // TODO find proper code
  SYMBOL_REQUIRED,              //  TSTACK_NOT_A_SYMBOL
  RATIONAL_REQUIRED,            //  TSTACK_NOT_A_RATIONAL
  TYPE_REQUIRED,                //  TSTACK_NOT_A_TYPE
  ARITH_ERROR,                  //  TSTACK_ARITH_ERROR
  DIVISION_BY_ZERO,             //  TSTACK_DIVIDE_BY_ZERO
  NON_CONSTANT_DIVISOR,         //  TSTACK_NON_CONSTANT_DIVISOR
  NEGATIVE_BVSIZE,              //  TSTACK_NONPOSITIVE_BVSIZE
  INCOMPATIBLE_BVSIZES,         //  TSTACK_INCOMPATIBLE_BVSIZES
  INVALID_BVCONSTANT,           //  TSTACK_INVALID_BVCONSTANT
  BVARITH_ERROR,                //  TSTACK_BVARITH_ERROR
  BVARITH_ERROR,                //  TSTACK_BVLOGIC_ERROR
  INVALID_FFCONSTANT,           //  TSTACK_INVALID_FFCONSTANT
  INVALID_FFSIZE,               //  TSTACK_INVALID_FFSIZE
  INCOMPATIBLE_FFSIZES,         //  TSTACK_INCOMPATIBLE_FFSIZES
  TYPE_MISMATCH_IN_DEF,         //  TSTACK_TYPE_ERROR_IN_DEFTERM
  YICES_NO_ERROR,                     //  TSTACK_STRINGS_ARE_NOT_TERMS
  YICES_NO_ERROR,                     //  TSTACK_VARIABLES_VALUES_NOT_MATCHING,  // TODO find proper code
  YICES_NO_ERROR,                     //  TSTACK_NOT_A_CONSTANT,  // TODO find proper code
  YICES_NO_ERROR,                     //  TSTACK_NOT_A_VARIABLE,  // TODO find proper code
  YICES_NO_ERROR,                     //  TSTACK_YICES_ERROR
};


/*
 * Store code and location data for an exception raised by tstack
 */
static void export_tstack_error(tstack_t *tstack, tstack_error_t exception) {
  error_report_t *error;

  error = yices_error_report(); //IAM: __yices_globals.error;
  error->line = tstack->error_loc.line;
  error->column = tstack->error_loc.column;
  if (exception != TSTACK_YICES_ERROR) {
    error->code = tstack_error2yices_error[exception];
    if (error->code == YICES_NO_ERROR) {
      report_bug("Internal error");
    }
  }
}


/*
 * Syntax error:
 * - lex = the lexer
 * - err = error file or NULL
 * - expected_token = what was expected or -1
 */
static void syntax_error(lexer_t *lex, FILE *err, int32_t expected_token) {
  yices_token_t tk;
  reader_t *rd;

  if (err == NULL) {
    export_syntax_error(lex, expected_token);
    return;
  }

  tk = current_token(lex);
  rd = &lex->reader;

  if (rd->name != NULL) {
    fprintf(err, "%s: ", rd->name);
  }

  switch (tk) {
  case TK_OPEN_STRING:
    fprintf(err, "missing string terminator \" (line %"PRId32", column %"PRId32")\n",
            rd->line, rd->column);
    break;

  case TK_EMPTY_BVCONST:
    fprintf(err, "invalid binary constant %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    break;

  case TK_EMPTY_HEXCONST:
    fprintf(err, "invalid hexadecimal constant %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    break;

  case TK_INVALID_NUM:
    fprintf(err, "invalid number %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    break;

  case TK_ZERO_DIVISOR:
    fprintf(err, "zero divisor in constant %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    break;

  case TK_ERROR:
    fprintf(err, "invalid token %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    break;

  default:
    // try to avoid confusion: don't want to print 'error not expected'
    if (expected_token == TK_NOT) {
      fprintf(err, "syntax error (line %"PRId32", column %"PRId32"): expected 'not'\n",
	      lex->tk_line, lex->tk_column);
    } else if (expected_token != -1) {
      assert(0 <= expected_token && expected_token < NUM_YICES_TOKENS);
      fprintf(err, "syntax error (line %"PRId32", column %"PRId32"): %s expected\n",
              lex->tk_line, lex->tk_column, yices_token_to_string(expected_token));
    } else {
      fprintf(err, "syntax error (line %"PRId32", column %"PRId32")\n",
              lex->tk_line, lex->tk_column);
    }
    break;
  }
}

// when we get (<symbol> ... ) and <symbol> is not a known command
static void syntax_error_bad_command(lexer_t *lex, FILE *err) {
  reader_t *rd;

  if (err == NULL) {
    export_syntax_error(lex, -1);
    return;
  }

  rd = &lex->reader;
  if (rd->name != NULL) {
    fprintf(err, "%s: ", rd->name);
  }
  fprintf(err, "syntax error: (line %"PRId32", column %"PRId32"): %s is not a command\n",
	  lex->tk_line, lex->tk_column, tkval(lex));
}


/*
 * Marker for bottom of the state stack.
 */
enum {
  done = NSTATES,
};


/*
 * Read action from the tables in yices_parse_tables.h
 */
static action_t get_action(state_t s, token_t tk) {
  int32_t i;

  i = base[s] + tk;
  if (check[i] == s) {
    return value[i];
  } else {
    return default_value[s];
  }
}


/*
 * Main parsing procedure
 * - start = initial state
 * - err = error output file or NULL
 * return -1 if there's an error, 0 otherwise
 */
static int32_t yices_parse(parser_t *parser, state_t start, FILE *err) {
  token_t token;
  parser_state_t state;
  parser_stack_t *stack;
  lexer_t *lex;
  tstack_t *tstack;
  int exception;
  loc_t loc;

  stack = &parser->pstack;
  lex = parser->lex;
  tstack = parser->tstack;

  assert(parser_stack_is_empty(stack));
  assert(tstack_is_empty(tstack) ||
         tstack->top_op == BUILD_TYPE ||
         tstack->top_op == BUILD_TERM);

  // prepare to catch exceptions in term stack operations
  exception = setjmp(tstack->env);
  if (exception == 0) {

    parser_push_state(stack, done);
    state = start;

  loop:
    // jump here for actions that consume the current token
    token = next_yices_token(lex);
    loc.line = current_token_line(lex);
    loc.column = current_token_column(lex);

    // jump here for actions that don't consume the token
  skip_token:
    switch (get_action(state, token)) {
    case next_goto_c1:
      state = c1;
      goto loop;

    case empty_command:
      tstack_push_op(tstack, EXIT_CMD, &loc);
      tstack_eval(tstack);
      state = parser_pop_state(stack);
      assert (state == done);
      goto the_end;

    case exit_next_goto_r0:
      tstack_push_op(tstack, EXIT_CMD, &loc);
      state = r0;
      goto loop;

    case check_next_goto_r0:
      tstack_push_op(tstack, CHECK_CMD, &loc);
      state = r0;
      goto loop;

    case check_assuming_next_goto_c16:
      tstack_push_op(tstack, CHECK_ASSUMING_CMD, &loc);
      state = c16;
      goto loop;

    case push_next_goto_r0:
      tstack_push_op(tstack, PUSH_CMD, &loc);
      state = r0;
      goto loop;

    case pop_next_goto_r0:
      tstack_push_op(tstack, POP_CMD, &loc);
      state = r0;
      goto loop;

    case reset_next_goto_r0:
      tstack_push_op(tstack, RESET_CMD, &loc);
      state = r0;
      goto loop;

    case dump_context_next_goto_r0:
      tstack_push_op(tstack, DUMP_CMD, &loc);
      state = r0;
      goto loop;

    case echo_next_goto_c3:
      tstack_push_op(tstack, ECHO_CMD, &loc);
      state = c3;
      goto loop;

    case include_next_goto_c3:
      tstack_push_op(tstack, INCLUDE_CMD, &loc);
      state = c3;
      goto loop;

    case assert_next_push_c20_goto_e0:
      tstack_push_op(tstack, ASSERT_CMD, &loc);
      parser_push_state(stack, c20);
      state = e0;
      goto loop;

    case deftype_next_goto_c2:
      tstack_push_op(tstack, DEF_YICES_TYPE, &loc);
      state = c2;
      goto loop;

    case defterm_next_goto_c6:
      tstack_push_op(tstack, DEF_YICES_TERM, &loc);
      state = c6;
      goto loop;

    case showmodel_next_goto_r0:
      tstack_push_op(tstack, SHOWMODEL_CMD, &loc);
      state = r0;
      goto loop;

    case eval_next_push_r0_goto_e0:
      tstack_push_op(tstack, EVAL_CMD, &loc);
      parser_push_state(stack, r0);
      state = e0;
      goto loop;

    case setparam_next_goto_c11:
      tstack_push_op(tstack, SET_PARAM_CMD, &loc);
      state = c11;
      goto loop;

    case showparam_next_goto_c13:
      tstack_push_op(tstack, SHOW_PARAM_CMD, &loc);
      state = c13;
      goto loop;

    case showparams_next_goto_r0:
      tstack_push_op(tstack, SHOW_PARAMS_CMD, &loc);
      state = r0;
      goto loop;

    case showstats_next_goto_r0:
      tstack_push_op(tstack, SHOW_STATS_CMD, &loc);
      state = r0;
      goto loop;

    case resetstats_next_goto_r0:
      tstack_push_op(tstack, RESET_STATS_CMD, &loc);
      state = r0;
      goto loop;

    case showtimeout_next_goto_r0:
      tstack_push_op(tstack, SHOW_TIMEOUT_CMD, &loc);
      state = r0;
      goto loop;

    case settimeout_next_goto_c14:
      tstack_push_op(tstack, SET_TIMEOUT_CMD, &loc);
      state = c14;
      goto loop;

    case help_next_goto_c15:
      tstack_push_op(tstack, HELP_CMD, &loc);
      state = c15;
      goto loop;

    case efsolve_next_goto_r0:
      tstack_push_op(tstack, EFSOLVE_CMD, &loc);
      state = r0;
      goto loop;

    case export_next_goto_c3:
      tstack_push_op(tstack, EXPORT_CMD, &loc);
      state = c3;
      goto loop;

    case implicant_next_goto_r0:
      tstack_push_op(tstack, SHOW_IMPLICANT_CMD, &loc);
      state = r0;
      goto loop;

    case unsat_core_next_goto_r0:
      tstack_push_op(tstack, SHOW_UNSAT_CORE_CMD, &loc);
      state = r0;
      goto loop;

    case unsat_assumptions_next_goto_r0:
      tstack_push_op(tstack, SHOW_UNSAT_ASSUMPTIONS_CMD, &loc);
      state = r0;
      goto loop;

    case reduced_model_next_goto_r0:
      tstack_push_op(tstack, SHOW_REDUCED_MODEL_CMD, &loc);
      state = r0;
      goto loop;

    case typename_next_goto_c10:
      // token must be a free typename (TK_SYMBOL)
      tstack_push_free_typename(tstack, tkval(lex), tklen(lex), &loc);
      state = c10;
      goto loop;

    case string_next_goto_r0:
      tstack_push_string(tstack, tkval(lex), tklen(lex), &loc);
      state = r0;
      goto loop;

    case termname_next_goto_c7:
      // token must be a free termname (TK_SYMBOL)
      tstack_push_free_termname(tstack, tkval(lex), tklen(lex), &loc);
      state = c7;
      goto loop;

    case next_push_c9_goto_t0:
      parser_push_state(stack, c9);
      state = t0;
      goto loop;

    case symbol_next_goto_c12:
      // symbol in (set-param <symbol> value)
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      state = c12;
      goto loop;

    case true_next_goto_r0:
      tstack_push_true(tstack, &loc);
      state = r0;
      goto loop;

    case false_next_goto_r0:
      tstack_push_false(tstack, &loc);
      state = r0;
      goto loop;

    case float_next_goto_r0:
      tstack_push_float(tstack, tkval(lex), &loc);
      state = r0;
      goto loop;

    case symbol_next_goto_r0:
      // symbol in (show-param <symbol>) or (help <symbol>)
      // or (set-param ... <symbol>)
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      state = r0;
      goto loop;

    case ret:
      assert(! parser_stack_is_empty(stack));
      // eval current operation
      tstack_eval(tstack);
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case push_r0_goto_e0:
      parser_push_state(stack, r0);
      state = e0;
      goto skip_token;

    case push_r0_goto_td0:
      parser_push_state(stack, r0);
      state = td0;
      goto skip_token;

    case symbol_next_goto_c16:
      // positive assumption in check-assuming
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      state = c16;
      goto loop;

    case next_goto_c17:
      state = c17;
      goto loop;

    case not_next_goto_c18:
      state = c18;
      goto loop;

    case symbol_next_goto_c19:
      // negative assumption in check-assuming
      tstack_push_not_symbol(tstack, tkval(lex), tklen(lex), &loc);
      state = c19;
      goto loop;

    case next_goto_c16:
      state = c16;
      goto loop;

    case int_return:
      tstack_push_int_type(tstack, &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case real_return:
      tstack_push_real_type(tstack, &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case bool_return:
      tstack_push_bool_type(tstack, &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case typesymbol_return:
      // TK_SYMBOL bound to a type
      tstack_push_type_by_name(tstack, tkval(lex), &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case next_goto_td1:
      state = td1;
      goto loop;

    case scalar_next_goto_td2:
      tstack_push_op(tstack, MK_SCALAR_TYPE, &loc);
      state = td2;
      goto loop;

    case bitvector_next_goto_t4:
      tstack_push_op(tstack, MK_BV_TYPE, &loc);
      state = t4;
      goto loop;

    case tuple_next_push_t6_goto_t0:
      tstack_push_op(tstack, MK_TUPLE_TYPE, &loc);
      parser_push_state(stack, t6);
      state = t0;
      goto loop;

    case arrow_next_push_t6_push_t0_goto_t0:
      tstack_push_op(tstack, MK_FUN_TYPE, &loc);
      parser_push_state(stack, t6);
      parser_push_state(stack, t0);
      state = t0;
      goto loop;

    case termname_next_goto_td3:
      // free termane in scalar definition
      tstack_push_free_termname(tstack, tkval(lex), tklen(lex), &loc);
      state = td3;
      goto loop;

    case next_goto_t1:
      state = t1;
      goto loop;

    case rational_next_goto_r0:
      tstack_push_rational(tstack, tkval(lex), &loc);
      state = r0;
      goto loop;

    case push_t6_goto_t0:
      parser_push_state(stack, t6);
      state = t0;
      goto skip_token;

    case true_return:
      tstack_push_true(tstack, &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case false_return:
      tstack_push_false(tstack, &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case rational_return:
      tstack_push_rational(tstack, tkval(lex), &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case float_return:
      tstack_push_float(tstack, tkval(lex), &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case bvbin_return:
      // skip prefix 0b
      assert(tklen(lex) > 2);
      tstack_push_bvbin(tstack, tkval(lex) + 2, tklen(lex) - 2, &loc);
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case bvhex_return:
      // skip prefix 0x
      assert(tklen(lex) > 2);
      tstack_push_bvhex(tstack, tkval(lex) + 2, tklen(lex) - 2, &loc);
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case termsymbol_return:
      // TK_SYMBOL bound to a term
      tstack_push_term_by_name(tstack, tkval(lex), &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case next_goto_e1:
      state = e1;
      goto loop;

      // all function keywords
    case if_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_ITE, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case eq_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_EQ, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case diseq_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_DISEQ, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case distinct_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_DISTINCT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case or_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_OR, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case and_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_AND, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case not_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_NOT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case xor_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_XOR, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case iff_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_IFF, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case implies_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_IMPLIES, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case mk_tuple_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_TUPLE, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case select_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_SELECT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case update_tuple_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_TUPLE_UPDATE, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case add_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_ADD, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case sub_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_SUB, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case mul_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_MUL, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case div_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_DIVISION, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case pow_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_POW, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case lt_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_LT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case le_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_LE, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case gt_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_GT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case ge_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_GE, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case mk_bv_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_CONST, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_add_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_ADD, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_sub_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SUB, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_mul_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_MUL, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_neg_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_NEG, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_pow_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_POW, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_not_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_NOT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_and_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_AND, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_or_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_OR, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_xor_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_XOR, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_nand_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_NAND, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_nor_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_NOR, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_xnor_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_XNOR, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_shift_left0_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SHIFT_LEFT0, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_shift_left1_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SHIFT_LEFT1, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_shift_right0_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SHIFT_RIGHT0, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_shift_right1_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SHIFT_RIGHT1, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_ashift_right_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_ASHIFT_RIGHT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_rotate_left_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_ROTATE_LEFT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_rotate_right_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_ROTATE_RIGHT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_extract_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_EXTRACT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_concat_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_CONCAT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_repeat_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_REPEAT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_sign_extend_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SIGN_EXTEND, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_zero_extend_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_ZERO_EXTEND, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_ge_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_GE, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_gt_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_GT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_le_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_LE, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_lt_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_LT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_sge_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SGE, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_sgt_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SGT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_sle_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SLE, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_slt_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SLT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_shl_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SHL, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_lshr_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_LSHR, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_ashr_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_ASHR, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_div_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_DIV, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_rem_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_REM, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_sdiv_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SDIV, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_srem_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SREM, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_smod_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_SMOD, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_redor_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_REDOR, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_redand_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_REDAND, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bv_comp_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BV_COMP, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bool_to_bv_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BOOL_TO_BV, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case bit_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_BIT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case floor_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_FLOOR, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case ceil_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_CEIL, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case abs_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_ABS, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case idiv_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_IDIV, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case mod_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_MOD, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case divides_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_DIVIDES, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case is_int_next_push_e3_goto_e0:
      tstack_push_op(tstack, MK_IS_INT, &loc);
      parser_push_state(stack, e3);
      state = e0;
      goto loop;

    case update_next_push_e5_goto_e0:
      tstack_push_op(tstack, MK_UPDATE, &loc);
      parser_push_state(stack, e5);
      state = e0;
      goto loop;

    case forall_next_goto_e10:
      tstack_push_op(tstack, MK_FORALL, &loc);
      state = e10;
      goto loop;

    case exists_next_goto_e10:
      tstack_push_op(tstack, MK_EXISTS, &loc);
      state = e10;
      goto loop;

    case lambda_next_goto_e10:
      tstack_push_op(tstack, MK_LAMBDA, &loc);
      state = e10;
      goto loop;

    case let_next_goto_e15:
      tstack_push_op(tstack, LET, &loc);
      state = e15;
      goto loop;

    case push_e3_push_e0_goto_e0:
      // uninterpreted function
      tstack_push_op(tstack, MK_APPLY, &loc);
      parser_push_state(stack, e3);
      parser_push_state(stack, e0);
      state = e0;
      goto skip_token;

    case push_e3_goto_e0:
      parser_push_state(stack, e3);
      state = e0;
      goto skip_token;

    case next_push_e7_goto_e0:
      parser_push_state(stack, e7);
      state = e0;
      goto loop;

    case next_push_r0_goto_e0:
      parser_push_state(stack, r0);
      state = e0;
      goto loop;

    case push_e7_goto_e0:
      parser_push_state(stack, e7);
      state = e0;
      goto skip_token;

    case next_goto_e11:
      state = e11;
      goto loop;

    case e11_varname_next_goto_e12:
      // first var decl in quantifiers
      tstack_push_op(tstack, DECLARE_VAR, &loc);
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      state = e12;
      goto loop;

    case next_push_e14_goto_t0:
      parser_push_state(stack, e14);
      state = t0;
      goto loop;

    case e14_varname_next_goto_e12:
      // var decl in quantifier except the first one
      tstack_eval(tstack); // eval previous binding
      // prepare for next var decl
      tstack_push_op(tstack, DECLARE_VAR, &loc);
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      state = e12;
      goto loop;

    case e14_next_push_r0_goto_e0:
      // end of var decls
      tstack_eval(tstack); // eval last binding
      parser_push_state(stack, r0);
      state = e0;
      goto loop;

    case bind_next_goto_e16:
      // start of <binding-list>
      tstack_push_op(tstack, BIND, &loc);
      state = e16;
      goto loop;

    case next_goto_e17:
      state = e17;
      goto loop;

    case termname_next_push_e19_goto_e0:
      // name in binding
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      parser_push_state(stack, e19);
      state = e0;
      goto loop;

    case next_goto_e20:
      // closing parenthesis in (<name> <term>) binding
      state = e20;
      goto loop;

    case close_next_push_r0_goto_e0:
      // end of <binding->list>
      tstack_eval(tstack); // evaluate the BIND
      parser_push_state(stack, r0);
      state = e0;
      goto  loop;

    case error_lpar_expected:
      syntax_error(lex, err, TK_LP);
      goto cleanup;

    case error_symbol_expected:
      syntax_error(lex, err, TK_SYMBOL);
      goto cleanup;

    case error_string_expected:
      syntax_error(lex, err, TK_STRING);
      goto cleanup;

    case error_colon_colon_expected:
      syntax_error(lex, err, TK_COLON_COLON);
      goto cleanup;

    case error_rational_expected:
      syntax_error(lex, err, TK_NUM_RATIONAL);
      goto cleanup;

    case error_rpar_expected:
      syntax_error(lex, err, TK_RP);
      goto cleanup;

    case error_not_expected:
      // this means that we got a token other than 'not'.
      syntax_error(lex, err, TK_NOT);
      goto cleanup;

    case error_not_a_command:
      syntax_error_bad_command(lex, err);
      goto cleanup;

    case error:
      syntax_error(lex, err, -1);
      goto cleanup;
    }

  } else {
    // exception raised by term_stack
    if (err == NULL) {
      export_tstack_error(tstack, exception);
    } else {
      term_stack_error(err, reader_name(lex), tstack, exception);
    }
    goto cleanup;
  }

 cleanup:
  tstack_reset(tstack);
  parser_stack_reset(stack);
  return -1;

 the_end:
  return 0;
}


/*
 * Top-level calls:
 */
extern int32_t parse_yices_command(parser_t *parser, FILE *err) {
  return yices_parse(parser, c0, err);
}

extern term_t parse_yices_term(parser_t *parser, FILE *err) {
  loc_t loc;

  loc.line = 0;
  loc.column = 0;
  tstack_push_op(parser->tstack, BUILD_TERM, &loc);
  if (yices_parse(parser, e0, err) < 0) {
    return NULL_TERM;
  }

  /*
   * Unless there's a bug somewhere. eval cannot generate an exception here.
   * (cf. eval_build_term in term_stack.c)
   */
  assert(parser->tstack->top_op == BUILD_TERM);
  tstack_eval(parser->tstack);

  assert(parser_stack_is_empty(&parser->pstack) &&
         tstack_is_empty(parser->tstack));

  return tstack_get_term(parser->tstack);
}


type_t parse_yices_type(parser_t *parser, FILE *err) {
  loc_t loc;

  loc.line = 0;
  loc.column = 0;
  tstack_push_op(parser->tstack, BUILD_TYPE, &loc);
  if (yices_parse(parser, td0, err) < 0) {
    return NULL_TYPE;
  }

  /*
   * Unless there's a bug somewhere. eval cannot generate an exception here.
   * (cf. eval_build_type in term_stack.c)
   */
  assert(parser->tstack->top_op == BUILD_TYPE);
  tstack_eval(parser->tstack);

  assert(parser_stack_is_empty(&parser->pstack) &&
         tstack_is_empty(parser->tstack));

  return tstack_get_type(parser->tstack);
}


