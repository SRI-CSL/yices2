/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Parser for the SMT-LIB 2.0 language
 */

#include <setjmp.h>
#include <inttypes.h>

#include "frontend/smt2/smt2_commands.h"
#include "frontend/smt2/smt2_lexer.h"
#include "frontend/smt2/smt2_parse_tables.h"
#include "frontend/smt2/smt2_parser.h"
#include "frontend/smt2/smt2_term_stack.h"

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
 * return -1 on error, 0 otherwise
 */
static int32_t smt2_parse(parser_t *parser, state_t start) {
  smt2_token_t token;
  smt2_keyword_t kw;
  parser_state_t state;
  parser_stack_t *stack;
  lexer_t *lex;
  tstack_t *tstack;
  int exception;
  loc_t loc;
  loc_t saved_loc; // used to store location of (as ...
  bool keep_tokens;
  etk_queue_t *token_queue;

  stack = &parser->pstack;
  lex = parser->lex;
  tstack = parser->tstack;

  assert(parser_stack_is_empty(stack));
  assert(tstack_is_empty(tstack));


  /*
   * keep_tokens: when true, all tokens received from the lexer are
   * pushed into the SMT2 global token queue. This enables SMT2
   * commands to print SMT2 expressions as they appear in the input.
   */
  keep_tokens = false;
  token_queue = NULL;

  // To catch exceptions in term-stack operations
  exception = setjmp(tstack->env);
  if (exception == 0) {
    parser_push_state(stack, done);
    state = start;

  loop:
    // jump here for actions that consume the current token
    token = next_smt2_token(lex);
    loc.line = current_token_line(lex);
    loc.column = current_token_column(lex);
    if (keep_tokens) {
      assert(token_queue != NULL);
      push_smt2_token(token_queue, token, tkval(lex), tklen(lex));
    }

  skip_token:
    // jump here for actions that don't consume the token
    switch (get_action(state, token)) {
    case next_goto_c1:
      state = c1;
      goto loop;

    case empty_command_return:
      tstack_push_op(tstack, SMT2_SILENT_EXIT, &loc);
      tstack_eval(tstack);
      state = parser_pop_state(stack);
      assert(state == done);
      goto the_end;

    case check_sat_next_goto_r0:
      tstack_push_op(tstack, SMT2_CHECK_SAT, &loc);
      state = r0;
      goto loop;

    case get_assertions_next_goto_r0:
      tstack_push_op(tstack, SMT2_GET_ASSERTIONS, &loc);
      state = r0;
      goto loop;

    case get_proof_next_goto_r0:
      tstack_push_op(tstack, SMT2_GET_PROOF, &loc);
      state = r0;
      goto loop;

    case get_unsat_core_next_goto_r0:
      tstack_push_op(tstack, SMT2_GET_UNSAT_CORE, &loc);
      state = r0;
      goto loop;

    case get_assignment_next_goto_r0:
      tstack_push_op(tstack, SMT2_GET_ASSIGNMENT, &loc);
      state = r0;
      goto loop;

    case exit_next_goto_r0:
      tstack_push_op(tstack, SMT2_EXIT, &loc);
      state = r0;
      goto loop;

    case push_next_goto_c3:
      tstack_push_op(tstack, SMT2_PUSH, &loc);
      state = c3;
      goto loop;

    case pop_next_goto_c3:
      tstack_push_op(tstack, SMT2_POP, &loc);
      state = c3;
      goto loop;

    case get_option_next_goto_c4:
      tstack_push_op(tstack, SMT2_GET_OPTION, &loc);
      state = c4;
      goto loop;

    case get_info_next_goto_c4:
      tstack_push_op(tstack, SMT2_GET_INFO, &loc);
      state = c4;
      goto loop;

    case set_logic_next_goto_c5:
      tstack_push_op(tstack, SMT2_SET_LOGIC, &loc);
      state = c5;
      goto loop;

    case set_option_next_goto_c6:
      tstack_push_op(tstack, SMT2_SET_OPTION, &loc);
      state = c6;
      goto loop;

    case set_info_next_goto_c6:
      tstack_push_op(tstack, SMT2_SET_INFO, &loc);
      state = c6;
      goto loop;

    case assert_next_push_r0_goto_t0:
      tstack_push_op(tstack, SMT2_ASSERT, &loc);
      parser_push_state(stack, r0);
      state = t0;
      goto loop;

    case declare_sort_next_goto_c8:
      tstack_push_op(tstack, SMT2_DECLARE_SORT, &loc);
      state = c8;
      goto loop;

    case define_sort_next_goto_c9:
      tstack_push_op(tstack, SMT2_DEFINE_SORT, &loc);
      state = c9;
      goto loop;

    case declare_fun_next_goto_c10:
      tstack_push_op(tstack, SMT2_DECLARE_FUN, &loc);
      state = c10;
      goto loop;

    case define_fun_next_goto_c11:
      tstack_push_op(tstack, SMT2_DEFINE_FUN, &loc);
      state = c11;
      goto loop;

    case get_value_next_goto_c12:
      /*
       * Activate the keep_tokens hack here
       * We push the two tokens '(' 'get-value' into the token_queue
       */
      keep_tokens = true;
      token_queue = smt2_token_queue();
      push_smt2_token(token_queue, SMT2_TK_LP, NULL, 0);
      push_smt2_token(token_queue, token, tkval(lex), tklen(lex));
      // now proceed as normal: push the command
      tstack_push_op(tstack, SMT2_GET_VALUE, &loc);
      state = c12;
      goto loop;

    case get_model_next_goto_r0:
      tstack_push_op(tstack, SMT2_GET_MODEL, &loc);
      state = r0;
      goto loop;

    case echo_next_goto_c13:
      tstack_push_op(tstack, SMT2_ECHO, &loc);
      state = c13;
      goto loop;

    case reset_next_goto_r0:
      tstack_push_op(tstack, SMT2_RESET, &loc);
      state = r0;
      goto loop;

    case numeral_next_goto_r0:
      tstack_push_rational(tstack, tkval(lex), &loc);
      state = r0;
      goto loop;

    case keyword_next_goto_r0:
    case symbol_next_goto_r0:
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      state = r0;
      goto loop;

    case keyword_next_goto_c6a:
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      state = c6a;
      goto loop;

    case next_return:
      // eval current command
      assert(! parser_stack_is_empty(stack));
      tstack_eval(tstack);
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
      // in (declare-sort <symbol> ..)
      //      tstack_push_free_type_or_macro_name(tstack, tkval(lex), tklen(lex), &loc);
      tstack_push_free_sort_name(tstack, tkval(lex), tklen(lex), &loc);
      state = c3;
      goto loop;

    case symbol_next_goto_c9a:
      // in (define-sort <symbol> ...)
      //      tstack_push_free_type_or_macro_name(tstack, tkval(lex), tklen(lex), &loc);
      tstack_push_free_sort_name(tstack, tkval(lex), tklen(lex), &loc);
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
      // in (define-sort .. (... <symbol> ...) ...)
      // type variable
      tstack_push_op(tstack, DECLARE_TYPE_VAR, &loc);
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      tstack_eval(tstack); // eval DECLARE_TYPE_VAR
      state = c9b;
      goto loop;

    case symbol_next_goto_c10a:
      // in (declare-fun <symbol> ...)
      //      tstack_push_free_termname(tstack, tkval(lex), tklen(lex), &loc);
      tstack_push_free_fun_name(tstack, tkval(lex), tklen(lex), &loc);
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
      // in (define-fun <symbol> ...)
      //      tstack_push_free_termname(tstack, tkval(lex), tklen(lex), &loc);
      tstack_push_free_fun_name(tstack, tkval(lex), tklen(lex), &loc);
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
      // in (define-fun ... ( .. (<symbol> <sort> ) ... ) ...)
      // variable of the given <sort>
      tstack_push_op(tstack, DECLARE_VAR, &loc);
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      parser_push_state(stack, c11f);
      state = s0;
      goto loop;

    case eval_next_goto_c11b:
      // evaluate the DECLARE_VAR
      tstack_eval(tstack);
      state = c11b;
      goto loop;

    case next_push_c12b_goto_t0:
      parser_push_state(stack, c12b);
      state = t0;
      goto loop;

    case string_next_goto_r0:
      // string argument to echo
      tstack_push_string(tstack, tkval(lex), tklen(lex), &loc);
      state = r0;
      goto loop;

    case next_goto_r0:
      state = r0;
      goto loop;

    case push_c12b_goto_t0:
      parser_push_state(stack, c12b);
      state = t0;
      goto skip_token;

    case numeral_next_return:
      tstack_push_rational(tstack, tkval(lex), &loc);
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case decimal_next_return:
      tstack_push_float(tstack, tkval(lex), &loc);
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case hexadecimal_next_return:
      // skip the prefix '#x'
      assert(tklen(lex) > 2);
      tstack_push_bvhex(tstack, tkval(lex) + 2, tklen(lex) - 2, &loc);
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case binary_next_return:
      // skip the prefix '#b'
      assert(tklen(lex) > 2);
      tstack_push_bvbin(tstack, tkval(lex) + 2, tklen(lex) - 2, &loc);
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case string_next_return:
      tstack_push_string(tstack, tkval(lex), tklen(lex), &loc);
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case symbol_next_return:
      // in attribute value
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case next_goto_a1:
      // start of s-expression as attribute value
      tstack_push_op(tstack, SMT2_MAKE_ATTR_LIST, &loc);
      state = a1;
      goto loop;

    case push_a1_goto_v0:
      parser_push_state(stack, a1);
      state = v0;
      goto skip_token;

    case keyword_next_return:
      // in attribute value
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case sort_symbol_next_return:
      // sort name
      tstack_push_sort_name(tstack, tkval(lex), tklen(lex), &loc);
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
      // sort constructor in ( <symbol> <sort> ... <sort> )
      tstack_push_sort_constructor(tstack, tkval(lex), tklen(lex), &loc);
      parser_push_state(stack, s10);
      state = s0;
      goto loop;

    case symbol_next_goto_s3:
      // indexed sort in (_ <symbol> <idx> .. <idx> )
      tstack_push_idx_sort(tstack, tkval(lex), tklen(lex), &loc);
      state = s3;
      goto loop;

    case numeral_next_goto_s4:
      // index in indexed sort
      tstack_push_rational(tstack, tkval(lex), &loc);
      state = s4;
      goto loop;

    case next_goto_s6:
      state = s6;
      goto loop;

    case symbol_next_goto_s7:
      // indexed sort constructor
      // in ((_ <symbol> <idx> ... <idx>) <sort> ... <sort>)
      tstack_push_idx_sort_constructor(tstack, tkval(lex), tklen(lex), &loc);
      state = s7;
      goto loop;

    case numeral_next_goto_s8:
      // <idx> in indexed sort constructor
      tstack_push_rational(tstack, tkval(lex), &loc);
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

    case term_symbol_next_return:
      // term name
      tstack_push_term_name(tstack, tkval(lex), tklen(lex), &loc);
      state = parser_pop_state(stack);
      if (state == done) {
        goto the_end;
      }
      goto loop;

    case next_goto_t1:
      state = t1;
      goto loop;

    case next_goto_t2:
      // (let
      tstack_push_op(tstack, LET, &loc);
      state = t2;
      goto loop;

    case forall_next_goto_t3:
      // (forall
      tstack_push_op(tstack, MK_FORALL, &loc);
      state = t3;
      goto loop;

    case exists_next_goto_t3:
      // (exists
      tstack_push_op(tstack, MK_EXISTS, &loc);
      state = t3;
      goto loop;

    case next_push_t4a_goto_t0:
      // (!
      tstack_push_op(tstack, SMT2_ADD_ATTRIBUTES, &loc);
      parser_push_state(stack, t4a);
      state = t0;
      goto loop;

    case next_goto_t5:
      // (as
      saved_loc = loc;
      state = t5;
      goto loop;

    case next_goto_t6:
      // ((
      state = t6;
      goto loop;

    case next_goto_t7:
      // (_
      state = t7;
      goto loop;

    case symbol_next_push_t8a_goto_t0:
      // function name in (<symbol> <term> .... <term>)
      tstack_push_smt2_op(tstack, tkval(lex), tklen(lex), &loc);
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
      // in (let (.. (<symbol> <term>) ...) ...)
      tstack_push_op(tstack, BIND, &loc);
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      parser_push_state(stack, t2d);
      state = t0;
      goto loop;

    case next_goto_t2e:
      tstack_eval(tstack); // eval the BIND
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
      // in (exists/forall (.. (<symbol <sort>) ...) ...)
      tstack_push_op(tstack, DECLARE_VAR, &loc);
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
      parser_push_state(stack, t3d);
      state = s0;
      goto loop;

    case next_goto_t3e:
      tstack_eval(tstack); // eval DECLARE_VAR
      state = t3e;
      goto loop;

    case check_keyword_then_branch:
      // in (! <term> .. <keyword> <attribute-value> ...)
      // We push the keyword in all cases as tstack's add_attributes requires a keyword.
      // We ignore anything other than :named or :pattern
      kw = smt2_string_to_keyword(tkval(lex), tklen(lex));
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
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
      // <symbol> as :named attribute
      // in (! <term> ... :named <symbol> ...)
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc);
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
      // in (as <symbol> <sort> )
      tstack_push_op(tstack, SMT2_SORTED_TERM, &saved_loc);
      tstack_push_qual_term_name(tstack, tkval(lex), tklen(lex), &loc);
      parser_push_state(stack, r0);
      state = s0;
      goto loop;

    case next_goto_t5b:
      state = t5b;
      goto loop;

    case symbol_next_goto_t5c:
      // in (as (_ <symbol> ...) <sort> )
      tstack_push_op(tstack, SMT2_SORTED_INDEXED_TERM, &saved_loc);
      tstack_push_qual_idx_term_name(tstack, tkval(lex), tklen(lex), &loc);
      state = t5c;
      goto loop;

    case numeral_next_goto_t5d:
      // push number
      tstack_push_rational(tstack, tkval(lex), &loc);
      state = t5d;
      goto loop;

    case next_goto_t6a:
      // ((as
      saved_loc = loc;
      state = t6a;
      goto loop;

    case next_goto_t6h:
      state = t6h;
      goto loop;

    case next_goto_t6b:
      state = t6b;
      goto loop;

    case symbol_next_push_t6g_goto_s0:
      // in ((as <symbol> <sort>) <arg> ... <arg>)
      tstack_push_op(tstack, SMT2_SORTED_APPLY, &saved_loc);
      tstack_push_qual_smt2_op(tstack, tkval(lex), tklen(lex), &loc);
      parser_push_state(stack, t6g);
      state = s0;
      goto loop;

    case next_goto_t6c:
      state = t6c;
      goto loop;

    case symbol_next_goto_t6d:
      // in ((as (_ <symbol> ...) <sort> ) <arg> ... <arg> )
      tstack_push_op(tstack, SMT2_SORTED_INDEXED_APPLY, &saved_loc);
      tstack_push_qual_smt2_idx_op(tstack, tkval(lex), tklen(lex), &loc);
      state = t6d;
      goto loop;

    case numeral_next_goto_t6e:
      tstack_push_rational(tstack, tkval(lex), &loc);
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
      // in ((_ <symbol> ,,, ) <arg> ... <arg> )
      tstack_push_smt2_idx_op(tstack, tkval(lex), tklen(lex), &loc);
      state = t6i;
      goto loop;

    case numeral_next_goto_t6j:
      tstack_push_rational(tstack, tkval(lex), &loc);
      state = t6j;
      goto loop;

    case symbol_next_goto_t7a:
      // in (_ <symbol> <idx> ... <idx> )
      tstack_push_idx_term(tstack, tkval(lex), tklen(lex), &loc);
      state = t7a;
      goto loop;

    case numeral_next_goto_t7b:
      tstack_push_rational(tstack, tkval(lex), &loc);
      state = t7b;
      goto loop;

    case push_t8a_goto_t0:
      parser_push_state(stack, t8a);
      state = t0;
      goto skip_token;

    case error_lp_expected:
      smt2_syntax_error(lex, SMT2_TK_LP);
      goto cleanup;

    case error_string_expected:
      smt2_syntax_error(lex, SMT2_TK_STRING);
      goto cleanup;

    case error_symbol_expected:
      smt2_syntax_error(lex, SMT2_TK_SYMBOL);
      goto cleanup;

    case error_numeral_expected:
      smt2_syntax_error(lex, SMT2_TK_NUMERAL);
      goto cleanup;

    case error_keyword_expected:
      smt2_syntax_error(lex, SMT2_TK_KEYWORD);
      goto cleanup;

    case error_rp_expected:
      smt2_syntax_error(lex, SMT2_TK_RP);
      goto cleanup;

    case error_underscore_expected:
      smt2_syntax_error(lex, SMT2_TK_UNDERSCORE);
      goto cleanup;

    case error_command_expected:
      smt2_syntax_error(lex, -2);
      goto cleanup;

    case error:
      smt2_syntax_error(lex, -1);
      goto cleanup;
    }

  } else {
    // exception from term_stack
    smt2_tstack_error(tstack, exception);
    goto cleanup;
  }

 cleanup:
  tstack_reset(tstack);
  parser_stack_reset(stack);
  if (keep_tokens) {
    reset_etk_queue(token_queue);
  }
  return -1;

 the_end:
  if (keep_tokens) {
    reset_etk_queue(token_queue);
  }
  return 0;
}


int32_t parse_smt2_command(parser_t *parser) {
  return smt2_parse(parser, c0);
}

