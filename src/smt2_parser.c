/*
 * Parser for the SMT-LIB 2.0 language
 */

#include <setjmp.h>
#include <inttypes.h>

#include "smt2_parse_tables.h"
#include "smt2_parser.h"
#include "smt2_lexer.h"


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
 * Syntax error:
 * - lex = lexer
 * - err = error file
 * - expected_token = either the token expected or -1
 */
static void syntax_error(lexer_t *lex, FILE *err, int32_t expected_token) {
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


/*
 * Marker for the bottom of the state stack
 */
enum {
  done = NSTATES,
};


/*
 * Read action from the tables in smt2_parse_tables.h
 */
static smt2_action_t get_action(state_t s, smt2_token_t tk) {
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
 * - err = error file for syntax errors
 * return -1 on error, 0 otherwise
 */
static int32_t smt2_parse(parser_t *parser, state_t start, FILE *err) {
  smt2_token_t token;
  smt2_keyword_t kw;
  parser_state_t state;
  parser_stack_t *stack;
  lexer_t *lex;
  tstack_t *tstack;
  int exception;
  //  loc_t loc;

  stack = &parser->pstack;
  lex = parser->lex;
  tstack = parser->tstack;

  assert(parser_stack_is_empty(stack));
  assert(tstack_is_empty(tstack));

  // To catch exceptions in term-stack operations
  exception = setjmp(tstack->env);
  if (exception == 0) {
    parser_push_state(stack, done);
    state = start;

  loop:
    // jump here for actions that consume the current token
    token = next_smt2_token(lex);
    //    loc.line = current_token_line(lex);
    //    loc.column = current_token_column(lex);

  skip_token:
    // jump here for actions that don't consume the token
    switch (get_action(state, token)) {
    case next_goto_c1:
      state = c1;
      goto loop;

    case empty_command_return:
      state = parser_pop_state(stack);
      assert(state == done);
      goto the_end;

    case check_sat_next_goto_r0:
      state = r0;
      goto loop;

    case get_assertions_next_goto_r0:
      state = r0;
      goto loop;

    case get_proof_next_goto_r0:
      state = r0;
      goto loop;

    case get_unsat_core_next_goto_r0:
      state = r0;
      goto loop;

    case get_assignment_next_goto_r0:
      state = r0;
      goto loop;

    case exit_next_goto_r0:
      state = r0;
      goto loop;

    case push_next_goto_c3:
      state = c3;
      goto loop;

    case pop_next_goto_c3:
      state = c3;
      goto loop;
      
    case get_option_next_goto_c4:
      state = c4;
      goto loop;

    case get_info_next_goto_c4:
      state = c4;
      goto loop;

    case set_logic_next_goto_c5:
      state = c5;
      goto loop;

    case set_option_next_goto_c6:
      state = c6;
      goto loop;

    case set_info_next_goto_c6:
      state = c6;
      goto loop;

    case assert_next_push_r0_goto_t0:
      parser_push_state(stack, r0);
      state = t0;
      goto loop;

    case declare_sort_next_goto_c8:
      state = c8;
      goto loop;

    case define_sort_next_goto_c9:
      state = c9;
      goto loop;

    case declare_fun_next_goto_c10:
      state = c10;
      goto loop;

    case define_fun_next_goto_c11:
      state = c11;
      goto loop;

    case get_value_next_goto_c12:
      state = c12;
      goto loop;
        
    case numeral_next_goto_r0:
      state = r0;
      goto loop;

    case keyword_next_goto_r0:
      state = r0;
      goto loop;

    case symbol_next_goto_r0:
      state = r0;
      goto loop;

    case keyword_next_goto_c6a:
      state = c6a;
      goto loop;

    case next_return:
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;
     
    case push_r0_goto_a0:
      parser_push_state(stack, r0);
      state = a0;
      goto skip_token;

    case symbol_next_goto_c3:
      state = c3;
      goto loop;

    case symbol_next_goto_c9a:
      state = c9a;
      goto loop;

    case next_goto_c9b:
      state = c9b;
      goto loop;

    case next_push_r0_goto_s0:
      parser_push_state(stack, r0);
      state = s0;
      goto loop;

    case symbol_next_goto_c9b:
      state = c9b;
      goto loop;

    case symbol_next_goto_c10a:
      state = c10a;
      goto loop;

    case next_goto_c10b:
      state = c10b;
      goto loop;

    case push_c10b_goto_s0:
      parser_push_state(stack, c10b);
      state = s0;
      goto skip_token;

    case symbol_next_goto_c11a:
      state = c11a;
      goto loop;

    case next_goto_c11b:
      state = c11b;
      goto loop;

    case next_push_r0_push_t0_goto_s0:
      parser_push_state(stack, r0);
      parser_push_state(stack, t0);
      state = s0;
      goto loop;

    case next_goto_c11d:
      state = c11d;
      goto loop;

    case symbol_next_push_c11f_goto_s0:
      parser_push_state(stack, c11f);
      state = s0;
      goto loop;

    case next_push_c12b_goto_t0:
      parser_push_state(stack, c12b);
      state = t0;
      goto loop;

    case next_goto_r0:
      state = r0;
      goto loop;

    case push_c12b_goto_t0:
      parser_push_state(stack, c12b);
      state = t0;
      goto skip_token;

    case numeral_next_return:
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case decimal_next_return:
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;
      
    case hexadecimal_next_return:
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;
     
    case binary_next_return:
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case string_next_return:
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case symbol_next_return:
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case next_goto_a1:
      state = a1;
      goto loop;

    case push_a1_goto_v0:
      parser_push_state(stack, a1);
      state = v0;
      goto skip_token;

    case keyword_next_return:
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case next_goto_s1:
      state = s1;
      goto loop;

    case next_goto_s2:
      state = s2;
      goto loop;
     
    case next_goto_s5:
      state = s5;
      goto loop;
     
    case symbol_next_push_s10_goto_s0:
      parser_push_state(stack, s10);
      state = s0;
      goto loop;
     
    case symbol_next_goto_s3:
      state = s3;
      goto loop;

    case numeral_next_goto_s4:
      state = s4;
      goto loop;

    case next_goto_s6:
      state = s6;
      goto loop;

    case symbol_next_goto_s7:
      state = s7;
      goto loop;

    case numeral_next_goto_s8:
      state = s8;
      goto loop;

    case next_push_s10_goto_s0:
      parser_push_state(stack, s10);
      state = s0;
      goto loop;

    case push_s10_goto_s0:
      parser_push_state(stack, s10);
      state = s0;
      goto skip_token;

    case next_goto_t1:
      state = t1;
      goto loop;

    case next_goto_t2:
      state = t2;
      goto loop;

    case forall_next_goto_t3:
      state = t3;
      goto loop;

    case exists_next_goto_t3:
      state = t3;
      goto loop;

    case next_push_t4a_goto_t0:
      parser_push_state(stack, t4a);
      state = t0;
      goto loop;

    case next_goto_t5:
      state = t5;
      goto loop;

    case next_goto_t6:
      state = t6;
      goto loop;

    case next_goto_t7:
      state = t7;
      goto loop;

    case symbol_next_push_t8a_goto_t0:
      parser_push_state(stack, t8a);
      state = t0;
      goto loop;

    case next_goto_t2a:
      state = t2a;
      goto loop;

    case next_goto_t2b:
      state = t2b;
      goto loop;

    case symbol_next_push_t2d_goto_t0:
      parser_push_state(stack, t2d);
      state = t0;
      goto loop;

    case next_goto_t2e:
      state = t2e;
      goto loop;

    case next_push_r0_goto_t0:
      parser_push_state(stack, r0);
      state = t0;
      goto loop;

    case next_goto_t3a:
      state = t3a;
      goto loop;

    case next_goto_t3b:
      state = t3b;
      goto loop;

    case symbol_next_push_t3d_goto_s0:
      parser_push_state(stack, t3d);
      state = s0;
      goto loop;

    case next_goto_t3e:
      state = t3e;
      goto loop;

    case check_keyword_then_branch:
      kw = smt2_string_to_keyword(tkval(lex), tklen(lex));
      if (kw == SMT2_KW_NAMED) {
        state = t4d;
      } else if (kw == SMT2_KW_PATTERN) {
        state = t4e;
      } else {
        state = t4b;
      }
      goto loop;
      
    case push_t4c_goto_a0:
      parser_push_state(stack, t4c);
      state = a0;
      goto skip_token;
     
    case symbol_next_goto_t4c:
      state = t4c;
      goto loop;

    case next_push_t4g_goto_t0:
      parser_push_state(stack, t4g);
      state = t0;
      goto loop;

    case next_goto_t4c:
      state = t4c;
      goto loop;

    case push_t4g_goto_t0:
      parser_push_state(stack, t4g);
      state = t0;
      goto skip_token;

    case next_goto_t5a:
      state = t5a;
      goto loop;

    case symbol_next_push_r0_goto_s0:
      parser_push_state(stack, r0);
      state = s0;
      goto loop;

    case next_goto_t5b:
      state = t5b;
      goto loop;

    case symbol_next_goto_t5c:
      state = t5c;
      goto loop;

    case numeral_next_goto_t5d:
      state = t5d;
      goto loop;

    case next_goto_t6a:
      state = t6a;
      goto loop;

    case next_goto_t6h:
      state = t6h;
      goto loop;

    case next_goto_t6b:
      state = t6b;
      goto loop;

    case symbol_next_push_t6g_goto_s0:
      parser_push_state(stack, t6g);
      state = s0;
      goto loop;

    case next_goto_t6c:
      state = t6c;
      goto loop;

    case symbol_next_goto_t6d:
      state = t6d;
      goto loop;

    case numeral_next_goto_t6e:
      state = t6e;
      goto loop;

    case next_push_t6g_goto_s0:
      parser_push_state(stack, t6g);
      state = s0;
      goto loop;
      
    case next_push_t8a_goto_t0:
      parser_push_state(stack, t8a);
      state = t0;
      goto loop;

    case symbol_next_goto_t6i:
      state = t6i;
      goto loop;

    case numeral_next_goto_t6j:
      state = t6j;
      goto loop;

    case symbol_next_goto_t7a:
      state = t7a;
      goto loop;

    case numeral_next_goto_t7b:
      state = t7b;
      goto loop;

    case push_t8a_goto_t0:
      parser_push_state(stack, t8a);
      state = t0;
      goto skip_token;

    case error_lp_expected:
      syntax_error(lex, err, SMT2_TK_LP);
      goto cleanup;

    case error_string_expected:
      syntax_error(lex, err, SMT2_TK_STRING);
      goto cleanup;

    case error_symbol_expected:
      syntax_error(lex, err, SMT2_TK_SYMBOL);
      goto cleanup;

    case error_numeral_expected:
      syntax_error(lex, err, SMT2_TK_NUMERAL);
      goto cleanup;

    case error_keyword_expected:
      syntax_error(lex, err, SMT2_TK_KEYWORD);
      goto cleanup;

    case error_rp_expected:
      syntax_error(lex, err, SMT2_TK_RP);
      goto cleanup;

    case error_underscore_expected:
      syntax_error(lex, err, SMT2_TK_UNDERSCORE);
      goto cleanup;
      
    case error:
      syntax_error(lex, err, -1);
      goto cleanup;
    }
   
  } else {
    // exception from term_stack
    goto cleanup;
  }

 cleanup:
  tstack_reset(tstack);
  parser_stack_reset(stack);
  return -1;

 the_end:
  return 0;
}


int32_t parse_smt2_command(parser_t *parser, FILE *err) {
  return smt2_parse(parser, c0, err);
}
