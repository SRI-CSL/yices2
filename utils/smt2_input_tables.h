/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

// token types
#include "frontend/smt2/smt2_lexer.h"

typedef enum state_s {
  c0, c1, c3, c4, c5, c6, c6a, c8, c9, c9a, c9b,
  c10, c10a, c10b, c11, c11a, c11b, c11d, c11f, c12, c12b, c13,
  a0, a1, v0,
  s0, s1, s2, s3, s4, s5, s6, s7, s8, s10,
  t0, t1, t2, t2a, t2b, t2d, t2e, 
  t3, t3a, t3b, t3d, t3e, 
  t4a, t4b, t4c, t4d, t4e, t4g,
  t5, t5a, t5b, t5c, t5d, 
  t6, t6a, t6b, t6c, t6d, t6e, t6g, t6h, t6i, t6j,
  t7, t7a, t7b, t8a,
  r0,
} state_t;

typedef struct {
  state_t source;
  token_t token;
  char *value;
} triple_t;

#define DEFAULT_TOKEN -1

/*
 * Action codes
 */
enum actions {
  // commands
  next_goto_c1,
  empty_command_return,
  check_sat_next_goto_r0,
  get_assertions_next_goto_r0,
  get_proof_next_goto_r0,
  get_unsat_core_next_goto_r0,
  get_assignment_next_goto_r0,
  exit_next_goto_r0,
  push_next_goto_c3,
  pop_next_goto_c3,
  get_option_next_goto_c4,
  get_info_next_goto_c4,
  set_logic_next_goto_c5,
  set_option_next_goto_c6,
  set_info_next_goto_c6,
  assert_next_push_r0_goto_t0,
  declare_sort_next_goto_c8,
  define_sort_next_goto_c9,
  declare_fun_next_goto_c10,
  define_fun_next_goto_c11,
  get_value_next_goto_c12,
  get_model_next_goto_r0,
  echo_next_goto_c13,
  reset_next_goto_r0,

  // arguments to the commands
  numeral_next_goto_r0,
  keyword_next_goto_r0,
  symbol_next_goto_r0,  
  keyword_next_goto_c6a,
  next_return,
  push_r0_goto_a0,
  symbol_next_goto_c3,
  symbol_next_goto_c9a,
  next_goto_c9b,
  next_push_r0_goto_s0,
  symbol_next_goto_c9b,
  symbol_next_goto_c10a,
  next_goto_c10b,
  push_c10b_goto_s0,
  symbol_next_goto_c11a,
  next_goto_c11b,
  next_push_r0_push_t0_goto_s0,
  next_goto_c11d,
  symbol_next_push_c11f_goto_s0,
  eval_next_goto_c11b,
  next_push_c12b_goto_t0,
  next_goto_r0,
  push_c12b_goto_t0,
  string_next_goto_r0,

  // attribute values + s-expressions
  numeral_next_return,
  decimal_next_return,
  hexadecimal_next_return,
  binary_next_return,
  string_next_return,
  symbol_next_return,
  next_goto_a1,
  push_a1_goto_v0,
  keyword_next_return,

  // sorts
  sort_sumbol_next_return,
  next_goto_s1,
  next_goto_s2,
  next_goto_s5,
  symbol_next_push_s10_goto_s0,
  symbol_next_goto_s3,
  numeral_next_goto_s4,
  next_goto_s6,
  symbol_next_goto_s7,
  numeral_next_goto_s8,
  next_push_s10_goto_s0,
  push_s10_goto_s0,

  // terms
  term_symbol_next_return,
  next_goto_t1,
  next_goto_t2,           // (let 
  forall_next_goto_t3,    // (forall
  exists_next_goto_t3,    // (exists
  next_push_t4a_goto_t0,  // (! 
  next_goto_t5,           // (as
  next_goto_t6,           // ((
  next_goto_t7,           // (_

  // simple function application (<symbol> <term> ... <term>)
  symbol_next_push_t8a_goto_t0,

  // (let ...
  next_goto_t2a,
  next_goto_t2b,
  symbol_next_push_t2d_goto_t0,
  next_goto_t2e,
  next_push_r0_goto_t0,

  // (exists ... and (forall ...
  next_goto_t3a,
  next_goto_t3b,
  symbol_next_push_t3d_goto_s0,
  next_goto_t3e,

  // (! <term> ...
  check_keyword_then_branch,
  push_t4c_goto_a0,
  symbol_next_goto_t4c,
  next_push_t4g_goto_t0,
  next_goto_t4c,
  push_t4g_goto_t0,

  // (as ...
  next_goto_t5a,
  symbol_next_push_r0_goto_s0,
  next_goto_t5b,
  symbol_next_goto_t5c,
  numeral_next_goto_t5d,

  // (( ...
  next_goto_t6a,
  next_goto_t6h,

  // ((as ...
  next_goto_t6b,
  symbol_next_push_t6g_goto_s0,
  next_goto_t6c,
  symbol_next_goto_t6d,
  numeral_next_goto_t6e,
  next_push_t6g_goto_s0,
  next_push_t8a_goto_t0,

  // ((_ ...
  symbol_next_goto_t6i,
  numeral_next_goto_t6j,
  
  // (_ ...
  symbol_next_goto_t7a,
  numeral_next_goto_t7b,
  
  // after <term> in a function application
  push_t8a_goto_t0,

  // errors
  error_lp_expected,
  error_string_expected,
  error_symbol_expected,
  error_numeral_expected,
  error_keyword_expected,
  error_rp_expected,
  error_underscore_expected,
  error_command_expected,
  error,
};

static triple_t triples[] = {
  { c0, SMT2_TK_LP, "next_goto_c1" },
  { c0, SMT2_TK_EOS, "empty_command_return" },
  { c0, DEFAULT_TOKEN, "error_lp_expected" },

  { c1, SMT2_TK_CHECK_SAT, "check_sat_next_goto_r0" },
  { c1, SMT2_TK_GET_ASSERTIONS, "get_assertions_next_goto_r0" },
  { c1, SMT2_TK_GET_PROOF, "get_proof_next_goto_r0" },
  { c1, SMT2_TK_GET_UNSAT_CORE, "get_unsat_core_next_goto_r0" },
  { c1, SMT2_TK_GET_ASSIGNMENT, "get_assignment_next_goto_r0" },
  { c1, SMT2_TK_EXIT, "exit_next_goto_r0" },
  { c1, SMT2_TK_PUSH, "push_next_goto_c3" },
  { c1, SMT2_TK_POP, "pop_next_goto_c3" },
  { c1, SMT2_TK_GET_OPTION, "get_option_next_goto_c4" },
  { c1, SMT2_TK_GET_INFO, "get_info_next_goto_c4" },
  { c1, SMT2_TK_SET_LOGIC, "set_logic_next_goto_c5" },
  { c1, SMT2_TK_SET_OPTION, "set_option_next_goto_c6" },
  { c1, SMT2_TK_SET_INFO, "set_info_next_goto_c6" },
  { c1, SMT2_TK_ASSERT, "assert_next_push_r0_goto_t0" },
  { c1, SMT2_TK_DECLARE_SORT, "declare_sort_next_goto_c8" },
  { c1, SMT2_TK_DEFINE_SORT, "define_sort_next_goto_c9" },
  { c1, SMT2_TK_DECLARE_FUN, "declare_fun_next_goto_c10" },
  { c1, SMT2_TK_DEFINE_FUN, "define_fun_next_goto_c11" },
  { c1, SMT2_TK_GET_VALUE, "get_value_next_goto_c12" },
  { c1, SMT2_TK_GET_MODEL, "get_model_next_goto_r0" },
  { c1, SMT2_TK_ECHO, "echo_next_goto_c13" },
  { c1, SMT2_TK_RESET, "reset_next_goto_r0" },
  { c1, DEFAULT_TOKEN, "error_command_expected" },

  { c3, SMT2_TK_NUMERAL, "numeral_next_goto_r0" },
  { c3, DEFAULT_TOKEN, "error_numeral_expected" },
  
  { c4, SMT2_TK_KEYWORD, "keyword_next_goto_r0" },
  { c4, DEFAULT_TOKEN, "error_keyword_expected" },

  { c5, SMT2_TK_SYMBOL, "symbol_next_goto_r0" },
  { c5, SMT2_TK_QSYMBOL, "symbol_next_goto_r0" },
  { c5, SMT2_TK_GET_MODEL, "symbol_next_goto_r0" },
  { c5, SMT2_TK_ECHO, "symbol_next_goto_r0" },
  { c5, SMT2_TK_RESET, "symbol_next_goto_r0" },
  { c5, DEFAULT_TOKEN, "error_symbol_expected" },

  { c6, SMT2_TK_KEYWORD, "keyword_next_goto_c6a" },
  { c6, DEFAULT_TOKEN, "error_keyword_expected" },

  { c6a, SMT2_TK_RP, "next_return" },
  { c6a, DEFAULT_TOKEN, "push_r0_goto_a0" },

  { c8, SMT2_TK_SYMBOL, "symbol_next_goto_c3" },
  { c8, SMT2_TK_QSYMBOL, "symbol_next_goto_c3" },
  { c8, SMT2_TK_GET_MODEL, "symbol_next_goto_c3" },
  { c8, SMT2_TK_ECHO, "symbol_next_goto_c3" },
  { c8, SMT2_TK_RESET, "symbol_next_goto_c3" },
  { c8, DEFAULT_TOKEN, "error_symbol_expected" },

  { c9, SMT2_TK_SYMBOL, "symbol_next_goto_c9a" },
  { c9, SMT2_TK_QSYMBOL, "symbol_next_goto_c9a" },
  { c9, SMT2_TK_GET_MODEL, "symbol_next_goto_c9a" },
  { c9, SMT2_TK_ECHO, "symbol_next_goto_c9a" },
  { c9, SMT2_TK_RESET, "symbol_next_goto_c9a" },
  { c9, DEFAULT_TOKEN, "error_symbol_expected" },

  { c9a, SMT2_TK_LP, "next_goto_c9b" },
  { c9a, DEFAULT_TOKEN, "error_lp_expected" },

  { c9b, SMT2_TK_RP, "next_push_r0_goto_s0" },
  { c9b, SMT2_TK_SYMBOL, "symbol_next_goto_c9b" },
  { c9b, SMT2_TK_QSYMBOL, "symbol_next_goto_c9b" },
  { c9b, SMT2_TK_GET_MODEL, "symbol_next_goto_c9b" },
  { c9b, SMT2_TK_ECHO, "symbol_next_goto_c9b" },
  { c9b, SMT2_TK_RESET, "symbol_next_goto_c9b" },

  { c10, SMT2_TK_SYMBOL, "symbol_next_goto_c10a" },
  { c10, SMT2_TK_QSYMBOL, "symbol_next_goto_c10a" },
  { c10, SMT2_TK_GET_MODEL, "symbol_next_goto_c10a" },
  { c10, SMT2_TK_ECHO, "symbol_next_goto_c10a" },
  { c10, SMT2_TK_RESET, "symbol_next_goto_c10a" },
  { c10, DEFAULT_TOKEN, "error_symbol_expected" },

  { c10a, SMT2_TK_LP, "next_goto_c10b" },
  { c10a, DEFAULT_TOKEN, "error_lp_expected" },

  { c10b, SMT2_TK_RP, "next_push_r0_goto_s0" },
  { c10b, DEFAULT_TOKEN, "push_c10b_goto_s0" },

  { c11, SMT2_TK_SYMBOL, "symbol_next_goto_c11a" },
  { c11, SMT2_TK_QSYMBOL, "symbol_next_goto_c11a" },
  { c11, SMT2_TK_GET_MODEL, "symbol_next_goto_c11a" },
  { c11, SMT2_TK_ECHO, "symbol_next_goto_c11a" },
  { c11, SMT2_TK_RESET, "symbol_next_goto_c11a" },
  { c11, DEFAULT_TOKEN, "error_symbol_expected" },

  { c11a, SMT2_TK_LP, "next_goto_c11b" },
  { c11a, DEFAULT_TOKEN, "error_lp_expected" },

  { c11b, SMT2_TK_RP, "next_push_r0_push_t0_goto_s0" },
  { c11b, SMT2_TK_LP, "next_goto_c11d" },

  { c11d, SMT2_TK_SYMBOL, "symbol_next_push_c11f_goto_s0" },
  { c11d, SMT2_TK_QSYMBOL, "symbol_next_push_c11f_goto_s0" },
  { c11d, SMT2_TK_GET_MODEL, "symbol_next_push_c11f_goto_s0" },
  { c11d, SMT2_TK_ECHO, "symbol_next_push_c11f_goto_s0" },
  { c11d, SMT2_TK_RESET, "symbol_next_push_c11f_goto_s0" },
  { c11d, DEFAULT_TOKEN, "error_symbol_expected" },

  { c11f, SMT2_TK_RP, "eval_next_goto_c11b" },
  { c11f, DEFAULT_TOKEN, "error_rp_expected" },

  { c12, SMT2_TK_LP, "next_push_c12b_goto_t0" },
  { c12, DEFAULT_TOKEN, "error_lp_expected" },

  { c12b, SMT2_TK_RP, "next_goto_r0" },
  { c12b, DEFAULT_TOKEN, "push_c12b_goto_t0" },

  { c13, SMT2_TK_STRING, "string_next_goto_r0" },

  { a0, SMT2_TK_NUMERAL, "numeral_next_return" },
  { a0, SMT2_TK_DECIMAL, "decimal_next_return" },
  { a0, SMT2_TK_HEXADECIMAL, "hexadecimal_next_return" },
  { a0, SMT2_TK_BINARY, "binary_next_return" },
  { a0, SMT2_TK_STRING, "string_next_return" },
  { a0, SMT2_TK_SYMBOL, "symbol_next_return" },
  { a0, SMT2_TK_QSYMBOL, "symbol_next_return" },
  { a0, SMT2_TK_GET_MODEL, "symbol_next_return" },
  { a0, SMT2_TK_ECHO, "symbol_next_return" },
  { a0, SMT2_TK_RESET, "symbol_next_return" },
  { a0, SMT2_TK_LP, "next_goto_a1" },

  { a1, SMT2_TK_RP, "next_return" },
  { a1, DEFAULT_TOKEN, "push_a1_goto_v0" },

  { v0, SMT2_TK_NUMERAL, "numeral_next_return" },
  { v0, SMT2_TK_DECIMAL, "decimal_next_return" },
  { v0, SMT2_TK_HEXADECIMAL, "hexadecimal_next_return" },
  { v0, SMT2_TK_BINARY, "binary_next_return" },
  { v0, SMT2_TK_STRING, "string_next_return" },
  { v0, SMT2_TK_SYMBOL, "symbol_next_return" },
  { v0, SMT2_TK_QSYMBOL, "symbol_next_return" },
  { v0, SMT2_TK_GET_MODEL, "symbol_next_return" },
  { v0, SMT2_TK_ECHO, "symbol_next_return" },
  { v0, SMT2_TK_RESET, "symbol_next_return" },
  { v0, SMT2_TK_KEYWORD, "keyword_next_return" },
  { v0, SMT2_TK_LP, "next_goto_a1" },

  { s0, SMT2_TK_SYMBOL, "sort_symbol_next_return" },
  { s0, SMT2_TK_QSYMBOL, "sort_symbol_next_return" },
  { s0, SMT2_TK_GET_MODEL, "sort_symbol_next_return" },
  { s0, SMT2_TK_ECHO, "sort_symbol_next_return" },
  { s0, SMT2_TK_RESET, "sort_symbol_next_return" },
  { s0, SMT2_TK_LP, "next_goto_s1" },

  { s1, SMT2_TK_UNDERSCORE, "next_goto_s2" },
  { s1, SMT2_TK_LP, "next_goto_s5" },
  { s1, SMT2_TK_SYMBOL, "symbol_next_push_s10_goto_s0" },
  { s1, SMT2_TK_QSYMBOL, "symbol_next_push_s10_goto_s0" },
  { s1, SMT2_TK_GET_MODEL, "symbol_next_push_s10_goto_s0" },
  { s1, SMT2_TK_ECHO, "symbol_next_push_s10_goto_s0" },
  { s1, SMT2_TK_RESET, "symbol_next_push_s10_goto_s0" },

  { s2, SMT2_TK_SYMBOL, "symbol_next_goto_s3" },
  { s2, SMT2_TK_QSYMBOL, "symbol_next_goto_s3" },
  { s2, SMT2_TK_GET_MODEL, "symbol_next_goto_s3" },
  { s2, SMT2_TK_ECHO, "symbol_next_goto_s3" },
  { s2, SMT2_TK_RESET, "symbol_next_goto_s3" },
  { s2, DEFAULT_TOKEN, "error_symbol_expected" },

  { s3, SMT2_TK_NUMERAL, "numeral_next_goto_s4" },
  { s3, DEFAULT_TOKEN, "error_numeral_expected" },

  { s4, SMT2_TK_RP, "next_return" },
  { s4, SMT2_TK_NUMERAL, "numeral_next_goto_s4" },

  { s5, SMT2_TK_UNDERSCORE, "next_goto_s6" },
  { s5, DEFAULT_TOKEN, "error_underscore_expected" },

  { s6, SMT2_TK_SYMBOL, "symbol_next_goto_s7" },
  { s6, SMT2_TK_QSYMBOL, "symbol_next_goto_s7" },
  { s6, SMT2_TK_GET_MODEL, "symbol_next_goto_s7" },
  { s6, SMT2_TK_ECHO, "symbol_next_goto_s7" },
  { s6, SMT2_TK_RESET, "symbol_next_goto_s7" },
  { s6, DEFAULT_TOKEN, "error_symbol_expected" },

  { s7, SMT2_TK_NUMERAL, "numeral_next_goto_s8" },
  { s7, DEFAULT_TOKEN, "error_numeral_expected" },

  { s8, SMT2_TK_RP, "next_push_s10_goto_s0" },
  { s8, SMT2_TK_NUMERAL, "numeral_next_goto_s8" },

  { s10, SMT2_TK_RP, "next_return" },
  { s10, DEFAULT_TOKEN, "push_s10_goto_s0" },

  { t0, SMT2_TK_NUMERAL, "numeral_next_return" },
  { t0, SMT2_TK_DECIMAL, "decimal_next_return" },
  { t0, SMT2_TK_HEXADECIMAL, "hexadecimal_next_return" },
  { t0, SMT2_TK_BINARY, "binary_next_return" },
  { t0, SMT2_TK_STRING, "string_next_return" },
  { t0, SMT2_TK_SYMBOL, "term_symbol_next_return" },
  { t0, SMT2_TK_QSYMBOL, "term_symbol_next_return" },
  { t0, SMT2_TK_GET_MODEL, "term_symbol_next_return" },
  { t0, SMT2_TK_ECHO, "term_symbol_next_return" },
  { t0, SMT2_TK_RESET, "term_symbol_next_return" },
  { t0, SMT2_TK_LP, "next_goto_t1" },

  { t1, SMT2_TK_LET, "next_goto_t2" },
  { t1, SMT2_TK_FORALL, "forall_next_goto_t3" },
  { t1, SMT2_TK_EXISTS, "exists_next_goto_t3" },
  { t1, SMT2_TK_BANG, "next_push_t4a_goto_t0" },
  { t1, SMT2_TK_AS, "next_goto_t5" },
  { t1, SMT2_TK_LP, "next_goto_t6" },
  { t1, SMT2_TK_UNDERSCORE, "next_goto_t7" },
  { t1, SMT2_TK_SYMBOL, "symbol_next_push_t8a_goto_t0" },
  { t1, SMT2_TK_QSYMBOL, "symbol_next_push_t8a_goto_t0" },
  { t1, SMT2_TK_GET_MODEL, "symbol_next_push_t8a_goto_t0" },
  { t1, SMT2_TK_ECHO, "symbol_next_push_t8a_goto_t0" },
  { t1, SMT2_TK_RESET, "symbol_next_push_t8a_goto_t0" },

  { t2, SMT2_TK_LP, "next_goto_t2a" },
  { t2, DEFAULT_TOKEN, "error_lp_expected" },

  { t2a, SMT2_TK_LP, "next_goto_t2b" },
  { t2a, DEFAULT_TOKEN, "error_lp_expected" },

  { t2b, SMT2_TK_SYMBOL, "symbol_next_push_t2d_goto_t0" },
  { t2b, SMT2_TK_QSYMBOL, "symbol_next_push_t2d_goto_t0" },
  { t2b, SMT2_TK_GET_MODEL, "symbol_next_push_t2d_goto_t0" },
  { t2b, SMT2_TK_ECHO, "symbol_next_push_t2d_goto_t0" },
  { t2b, SMT2_TK_RESET, "symbol_next_push_t2d_goto_t0" },
  { t2b, DEFAULT_TOKEN, "error_symbol_expected" },

  { t2d, SMT2_TK_RP, "next_goto_t2e" },
  { t2d, DEFAULT_TOKEN, "error_rp_expected" },

  { t2e, SMT2_TK_LP, "next_goto_t2b" },
  { t2e, SMT2_TK_RP, "next_push_r0_goto_t0" },

  { t3, SMT2_TK_LP, "next_goto_t3a" },
  { t3, DEFAULT_TOKEN, "error_lp_expected" },

  { t3a, SMT2_TK_LP, "next_goto_t3b" },
  { t3a, DEFAULT_TOKEN, "error_lp_expected" },

  { t3b, SMT2_TK_SYMBOL, "symbol_next_push_t3d_goto_s0" },
  { t3b, SMT2_TK_QSYMBOL, "symbol_next_push_t3d_goto_s0" },
  { t3b, SMT2_TK_GET_MODEL, "symbol_next_push_t3d_goto_s0" },
  { t3b, SMT2_TK_ECHO, "symbol_next_push_t3d_goto_s0" },
  { t3b, SMT2_TK_RESET, "symbol_next_push_t3d_goto_s0" },
  { t3b, DEFAULT_TOKEN, "error_symbol_expected" },

  { t3d, SMT2_TK_RP, "next_goto_t3e" },
  { t3d, DEFAULT_TOKEN, "error_rp_expected" },

  { t3e, SMT2_TK_LP, "next_goto_t3b" },
  { t3e, SMT2_TK_RP, "next_push_r0_goto_t0" },

  { t4a, SMT2_TK_KEYWORD, "check_keyword_then_branch" },
  { t4a, DEFAULT_TOKEN, "error_keyword_expected" },

  { t4b, SMT2_TK_RP, "next_return" },
  { t4b, SMT2_TK_KEYWORD, "check_keyword_then_branch" },
  { t4b, DEFAULT_TOKEN, "push_t4c_goto_a0" },

  { t4c, SMT2_TK_RP, "next_return" },
  { t4c, SMT2_TK_KEYWORD, "check_keyword_then_branch" },

  { t4d, SMT2_TK_SYMBOL, "symbol_next_goto_t4c" },
  { t4d, SMT2_TK_QSYMBOL, "symbol_next_goto_t4c" },
  { t4d, SMT2_TK_GET_MODEL, "symbol_next_goto_t4c" },
  { t4d, SMT2_TK_ECHO, "symbol_next_goto_t4c" },
  { t4d, SMT2_TK_RESET, "symbol_next_goto_t4c" },
  { t4d, DEFAULT_TOKEN, "error_symbol_expected" },

  { t4e, SMT2_TK_LP, "next_push_t4g_goto_t0" },
  { t4e, DEFAULT_TOKEN, "error_lp_expected" },

  { t4g, SMT2_TK_RP, "next_goto_t4c" },
  { t4g, DEFAULT_TOKEN, "push_t4g_goto_t0" },

  { t5, SMT2_TK_LP, "next_goto_t5a" },
  { t5, SMT2_TK_SYMBOL, "symbol_next_push_r0_goto_s0" },
  { t5, SMT2_TK_QSYMBOL, "symbol_next_push_r0_goto_s0" },
  { t5, SMT2_TK_GET_MODEL, "symbol_next_push_r0_goto_s0" },
  { t5, SMT2_TK_ECHO, "symbol_next_push_r0_goto_s0" },
  { t5, SMT2_TK_RESET, "symbol_next_push_r0_goto_s0" },

  { t5a, SMT2_TK_UNDERSCORE, "next_goto_t5b" },
  { t5a, DEFAULT_TOKEN, "error_underscore_expected" },

  { t5b, SMT2_TK_SYMBOL, "symbol_next_goto_t5c" },
  { t5b, SMT2_TK_QSYMBOL, "symbol_next_goto_t5c" },
  { t5b, SMT2_TK_GET_MODEL, "symbol_next_goto_t5c" },
  { t5b, SMT2_TK_ECHO, "symbol_next_goto_t5c" },
  { t5b, SMT2_TK_RESET, "symbol_next_goto_t5c" },
  { t5b, DEFAULT_TOKEN, "error_symbol_expected" },

  { t5c, SMT2_TK_NUMERAL, "numeral_next_goto_t5d" },
  { t5c, DEFAULT_TOKEN, "error_numeral_expected" },

  { t5d, SMT2_TK_NUMERAL, "numeral_next_goto_t5d" },
  { t5d, SMT2_TK_RP, "next_push_r0_goto_s0" },

  { t6, SMT2_TK_AS, "next_goto_t6a" },
  { t6, SMT2_TK_UNDERSCORE, "next_goto_t6h" },

  { t6a, SMT2_TK_LP, "next_goto_t6b" },
  { t6a, SMT2_TK_SYMBOL, "symbol_next_push_t6g_goto_s0" },
  { t6a, SMT2_TK_QSYMBOL, "symbol_next_push_t6g_goto_s0" },
  { t6a, SMT2_TK_GET_MODEL, "symbol_next_push_t6g_goto_s0" },
  { t6a, SMT2_TK_ECHO, "symbol_next_push_t6g_goto_s0" },
  { t6a, SMT2_TK_RESET, "symbol_next_push_t6g_goto_s0" },
 
  { t6b, SMT2_TK_UNDERSCORE, "next_goto_t6c" },
  { t6b, DEFAULT_TOKEN, "error_underscore_expected" },

  { t6c, SMT2_TK_SYMBOL, "symbol_next_goto_t6d" },
  { t6c, SMT2_TK_QSYMBOL, "symbol_next_goto_t6d" },
  { t6c, SMT2_TK_GET_MODEL, "symbol_next_goto_t6d" },
  { t6c, SMT2_TK_ECHO, "symbol_next_goto_t6d" },
  { t6c, SMT2_TK_RESET, "symbol_next_goto_t6d" },
  { t6c, DEFAULT_TOKEN, "error_symbol_expected" },

  { t6d, SMT2_TK_NUMERAL, "numeral_next_goto_t6e" },
  { t6d, DEFAULT_TOKEN, "error_numeral_expected" },

  { t6e, SMT2_TK_NUMERAL, "numeral_next_goto_t6e" },
  { t6e, SMT2_TK_RP, "next_push_t6g_goto_s0" },

  { t6g, SMT2_TK_RP, "next_push_t8a_goto_t0" },
  { t6g, DEFAULT_TOKEN, "error_rp_expected" },

  { t6h, SMT2_TK_SYMBOL, "symbol_next_goto_t6i" },
  { t6h, SMT2_TK_QSYMBOL, "symbol_next_goto_t6i" },
  { t6h, SMT2_TK_GET_MODEL, "symbol_next_goto_t6i" },
  { t6h, SMT2_TK_ECHO, "symbol_next_goto_t6i" },
  { t6h, SMT2_TK_RESET, "symbol_next_goto_t6i" },
  { t6h, DEFAULT_TOKEN, "error_symbol_expected" },

  { t6i, SMT2_TK_NUMERAL, "numeral_next_goto_t6j" },
  { t6i, DEFAULT_TOKEN, "error_numeral_expected" },

  { t6j, SMT2_TK_NUMERAL, "numeral_next_goto_t6j" },
  { t6j, SMT2_TK_RP, "next_push_t8a_goto_t0" },

  { t7, SMT2_TK_SYMBOL, "symbol_next_goto_t7a" },
  { t7, SMT2_TK_QSYMBOL, "symbol_next_goto_t7a" },
  { t7, SMT2_TK_GET_MODEL, "symbol_next_goto_t7a" },
  { t7, SMT2_TK_ECHO, "symbol_next_goto_t7a" },
  { t7, SMT2_TK_RESET, "symbol_next_goto_t7a" },
  { t7, DEFAULT_TOKEN, "error_symbol_expected" },

  { t7a, SMT2_TK_NUMERAL, "numeral_next_goto_t7b" },
  { t7a, DEFAULT_TOKEN, "error_numeral_expected" },

  { t7b, SMT2_TK_RP,  "next_return" },
  { t7b, SMT2_TK_NUMERAL, "numeral_next_goto_t7b" },

  { t8a, SMT2_TK_RP, "next_return" },
  { t8a, DEFAULT_TOKEN, "push_t8a_goto_t0" },

  { r0, SMT2_TK_RP, "next_return" },
  { r0, DEFAULT_TOKEN, "error_rp_expected" },

  { -1, -1, NULL },
};


#define NSTATES (r0+1)
#define NTOKENS (SMT2_TK_ERROR+1)
#define DEFAULT_VALUE "error"
