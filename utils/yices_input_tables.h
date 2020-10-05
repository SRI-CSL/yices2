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

// get token type
#include "frontend/yices/yices_lexer.h"

typedef enum state_s {
  r0,
  c0, c1, c2, c3, c6, c7, c9, c10, c11, c12, c13,
  c14, c15, c16, c17, c18, c19, c20,
  td0, td1, td2, td3,
  t0, t1, t4, t6,
  e0, e1, e3, e5, e7, e10, e11, e12, e14, e15, e16, e17, e19, e20,
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
  next_goto_c1,
  empty_command,
  exit_next_goto_r0,
  check_next_goto_r0,
  check_assuming_next_goto_c16,
  push_next_goto_r0,
  pop_next_goto_r0,
  reset_next_goto_r0,
  dump_context_next_goto_r0,
  echo_next_goto_c3,
  include_next_goto_c3,
  assert_next_push_c20_goto_e0,
  deftype_next_goto_c2,
  defterm_next_goto_c6,
  showmodel_next_goto_r0,
  eval_next_push_r0_goto_e0,
  setparam_next_goto_c11,
  showparam_next_goto_c13,
  showparams_next_goto_r0,
  showstats_next_goto_r0,
  resetstats_next_goto_r0,
  showtimeout_next_goto_r0,
  settimeout_next_goto_c14,
  help_next_goto_c15,
  efsolve_next_goto_r0,    // New command: (ef-solve)
  export_next_goto_c3,     // New command: (export-to-dimacs filename)
  implicant_next_goto_r0,  // New command: (show-implicant)
  unsat_core_next_goto_r0, // (show-unsat-core)
  unsat_assumptions_next_goto_r0, // (show-unsat-assumptions)
  reduced_model_next_goto_r0,     // (show-reduced-model)

  typename_next_goto_c10,  // token must be a free typename (TK_SYMBOL)
  string_next_goto_r0,     // string argument to echo, include, help, export
  termname_next_goto_c7,   // token must be a free termname (TK_SYMBOL)
  next_push_c9_goto_t0,
  symbol_next_goto_c12,    // in (set-param <symbol> ...)
  true_next_goto_r0,       // in (set-param ... true)
  false_next_goto_r0,      // in (set-param ... false)
  float_next_goto_r0,      // in (set-param ... <float>)
  symbol_next_goto_r0,     // in (show-param <symbol>) or (help <symbol>) or (set-param ... <symbol>)
  ret,                     // return
  push_r0_goto_e0,
  push_r0_goto_td0,

  symbol_next_goto_c16,    // positive assumption
  next_goto_c17,
  not_next_goto_c18,
  symbol_next_goto_c19,   // negated assumption
  next_goto_c16,

  int_return,
  real_return,
  bool_return,
  typesymbol_return,      // TK_SYMBOL bound to a type
  next_goto_td1,
  scalar_next_goto_td2,
  bitvector_next_goto_t4,
  tuple_next_push_t6_goto_t0,
  arrow_next_push_t6_push_t0_goto_t0,
  termname_next_goto_td3,  // free termane in scalar definition

  next_goto_t1,
  rational_next_goto_r0,
  push_t6_goto_t0,

  true_return,
  false_return,
  rational_return,
  float_return,
  bvbin_return,
  bvhex_return,
  termsymbol_return,     // TK_SYMBOL bound to a term
  next_goto_e1,

  // all function keywords
  if_next_push_e3_goto_e0,
  eq_next_push_e3_goto_e0,
  diseq_next_push_e3_goto_e0,
  distinct_next_push_e3_goto_e0,
  or_next_push_e3_goto_e0,
  and_next_push_e3_goto_e0,
  not_next_push_e3_goto_e0,
  xor_next_push_e3_goto_e0,
  iff_next_push_e3_goto_e0,
  implies_next_push_e3_goto_e0,
  mk_tuple_next_push_e3_goto_e0,
  select_next_push_e3_goto_e0,
  update_tuple_next_push_e3_goto_e0,
  add_next_push_e3_goto_e0,
  sub_next_push_e3_goto_e0,
  mul_next_push_e3_goto_e0,
  div_next_push_e3_goto_e0,
  pow_next_push_e3_goto_e0,
  lt_next_push_e3_goto_e0,
  le_next_push_e3_goto_e0,
  gt_next_push_e3_goto_e0,
  ge_next_push_e3_goto_e0,
  mk_bv_next_push_e3_goto_e0,
  bv_add_next_push_e3_goto_e0,
  bv_sub_next_push_e3_goto_e0,
  bv_mul_next_push_e3_goto_e0,
  bv_neg_next_push_e3_goto_e0,
  bv_pow_next_push_e3_goto_e0,
  bv_not_next_push_e3_goto_e0,
  bv_and_next_push_e3_goto_e0,
  bv_or_next_push_e3_goto_e0,
  bv_xor_next_push_e3_goto_e0,
  bv_nand_next_push_e3_goto_e0,
  bv_nor_next_push_e3_goto_e0,
  bv_xnor_next_push_e3_goto_e0,
  bv_shift_left0_next_push_e3_goto_e0,
  bv_shift_left1_next_push_e3_goto_e0,
  bv_shift_right0_next_push_e3_goto_e0,
  bv_shift_right1_next_push_e3_goto_e0,
  bv_ashift_right_next_push_e3_goto_e0,
  bv_rotate_left_next_push_e3_goto_e0,
  bv_rotate_right_next_push_e3_goto_e0,
  bv_extract_next_push_e3_goto_e0,
  bv_concat_next_push_e3_goto_e0,
  bv_repeat_next_push_e3_goto_e0,
  bv_sign_extend_next_push_e3_goto_e0,
  bv_zero_extend_next_push_e3_goto_e0,
  bv_ge_next_push_e3_goto_e0,
  bv_gt_next_push_e3_goto_e0,
  bv_le_next_push_e3_goto_e0,
  bv_lt_next_push_e3_goto_e0,
  bv_sge_next_push_e3_goto_e0,
  bv_sgt_next_push_e3_goto_e0,
  bv_sle_next_push_e3_goto_e0,
  bv_slt_next_push_e3_goto_e0,
  bv_shl_next_push_e3_goto_e0,
  bv_lshr_next_push_e3_goto_e0,
  bv_ashr_next_push_e3_goto_e0,
  bv_div_next_push_e3_goto_e0,
  bv_rem_next_push_e3_goto_e0,
  bv_sdiv_next_push_e3_goto_e0,
  bv_srem_next_push_e3_goto_e0,
  bv_smod_next_push_e3_goto_e0,
  bv_redor_next_push_e3_goto_e0,
  bv_redand_next_push_e3_goto_e0,
  bv_comp_next_push_e3_goto_e0,
  bool_to_bv_next_push_e3_goto_e0,
  bit_next_push_e3_goto_e0,
  floor_next_push_e3_goto_e0,
  ceil_next_push_e3_goto_e0,
  abs_next_push_e3_goto_e0,
  idiv_next_push_e3_goto_e0,
  mod_next_push_e3_goto_e0,
  divides_next_push_e3_goto_e0,
  is_int_next_push_e3_goto_e0,

  update_next_push_e5_goto_e0,
  forall_next_goto_e10,
  exists_next_goto_e10,
  lambda_next_goto_e10,
  let_next_goto_e15,
  push_e3_push_e0_goto_e0,

  push_e3_goto_e0,
  next_push_e7_goto_e0,
  next_push_r0_goto_e0,
  push_e7_goto_e0,
  next_goto_e11,
  e11_varname_next_goto_e12,       // first var decl in quantifiers
  next_push_e14_goto_t0,
  e14_varname_next_goto_e12,       // var decl in quantifier except the first one
  e14_next_push_r0_goto_e0,        // end of var decls

  bind_next_goto_e16,              // start of <binding-list>
  next_goto_e17,
  termname_next_push_e19_goto_e0,  // name in binding
  next_goto_e20,
  close_next_push_r0_goto_e0,      // end of <binding-list>

  error_lpar_expected,
  error_symbol_expected,
  error_string_expected,
  error_colon_colon_expected,
  error_rational_expected,
  error_rpar_expected,
  error_not_expected,
  error_not_a_command,
  error,
};

static triple_t triples[] = {
  { c0, TK_LP, "next_goto_c1" },
  { c0, TK_EOS, "empty_command" },
  { c0, DEFAULT_TOKEN, "error_lpar_expected" },

  { c1, TK_EXIT, "exit_next_goto_r0" },
  { c1, TK_CHECK, "check_next_goto_r0" },
  { c1, TK_CHECK_ASSUMING, "check_assuming_next_goto_c16" },
  { c1, TK_PUSH, "push_next_goto_r0" },
  { c1, TK_POP, "pop_next_goto_r0" },
  { c1, TK_RESET, "reset_next_goto_r0" },
  { c1, TK_DUMP_CONTEXT, "dump_context_next_goto_r0" },
  { c1, TK_ECHO, "echo_next_goto_c3" },
  { c1, TK_INCLUDE, "include_next_goto_c3" },
  { c1, TK_ASSERT, "assert_next_push_c20_goto_e0" },
  { c1, TK_DEFINE_TYPE, "deftype_next_goto_c2" },
  { c1, TK_DEFINE, "defterm_next_goto_c6" },
  { c1, TK_SHOW_MODEL, "showmodel_next_goto_r0" },
  { c1, TK_EVAL, "eval_next_push_r0_goto_e0" },
  { c1, TK_SET_PARAM, "setparam_next_goto_c11" },
  { c1, TK_SHOW_PARAM, "showparam_next_goto_c13" },
  { c1, TK_SHOW_PARAMS, "showparams_next_goto_r0" },
  { c1, TK_SHOW_STATS, "showstats_next_goto_r0" },
  { c1, TK_SHOW_TIMEOUT, "showtimeout_next_goto_r0" },
  { c1, TK_RESET_STATS, "resetstats_next_goto_r0" },
  { c1, TK_SET_TIMEOUT, "settimeout_next_goto_c14" },
  { c1, TK_HELP, "help_next_goto_c15" },
  { c1, TK_EF_SOLVE, "efsolve_next_goto_r0" },
  { c1, TK_EXPORT_TO_DIMACS, "export_next_goto_c3" },
  { c1, TK_SHOW_IMPLICANT, "implicant_next_goto_r0" },
  { c1, TK_SHOW_UNSAT_CORE, "unsat_core_next_goto_r0" },
  { c1, TK_SHOW_UNSAT_ASSUMPTIONS, "unsat_assumptions_next_goto_r0" },
  { c1, TK_SHOW_REDUCED_MODEL, "reduced_model_next_goto_r0" },
  { c1, TK_SYMBOL, "error_not_a_command" },

  { c2, TK_SYMBOL, "typename_next_goto_c10" },
  { c2, DEFAULT_TOKEN, "error_symbol_expected" },

  { c3, TK_STRING, "string_next_goto_r0" },
  { c3, DEFAULT_TOKEN, "error_string_expected" },

  { c6, TK_SYMBOL, "termname_next_goto_c7" },
  { c6, DEFAULT_TOKEN, "error_symbol_expected" },

  { c7, TK_COLON_COLON, "next_push_c9_goto_t0" },
  { c7, DEFAULT_TOKEN, "error_colon_colon_expected" },

  { c9, TK_RP, "ret" },
  { c9, DEFAULT_TOKEN, "push_r0_goto_e0" },

  { c10, TK_RP, "ret" },
  { c10, DEFAULT_TOKEN, "push_r0_goto_td0" },

  { c11, TK_SYMBOL, "symbol_next_goto_c12" },
  { c11, DEFAULT_TOKEN, "error_symbol_expected" },

  { c12, TK_TRUE, "true_next_goto_r0" },
  { c12, TK_FALSE, "false_next_goto_r0" },
  { c12, TK_NUM_RATIONAL, "rational_next_goto_r0" },
  { c12, TK_NUM_FLOAT, "float_next_goto_r0" },
  { c12, TK_SYMBOL, "symbol_next_goto_r0" },

  { c13, TK_SYMBOL, "symbol_next_goto_r0" },

  { c14, TK_NUM_RATIONAL, "rational_next_goto_r0" },

  // c15: parameters to (help ...): treat all keywords as symbols here
  { c15, TK_DEFINE_TYPE, "symbol_next_goto_r0" },
  { c15, TK_DEFINE, "symbol_next_goto_r0" },
  { c15, TK_ASSERT, "symbol_next_goto_r0" },
  { c15, TK_CHECK, "symbol_next_goto_r0" },
  { c15, TK_CHECK_ASSUMING, "symbol_next_goto_r0" },
  { c15, TK_PUSH, "symbol_next_goto_r0" },
  { c15, TK_POP, "symbol_next_goto_r0" },
  { c15, TK_RESET, "symbol_next_goto_r0" },
  { c15, TK_DUMP_CONTEXT, "symbol_next_goto_r0" },
  { c15, TK_EXIT, "symbol_next_goto_r0" },
  { c15, TK_ECHO, "symbol_next_goto_r0" },
  { c15, TK_INCLUDE, "symbol_next_goto_r0" },
  { c15, TK_SHOW_MODEL, "symbol_next_goto_r0" },
  { c15, TK_EVAL, "symbol_next_goto_r0" },
  { c15, TK_SET_PARAM, "symbol_next_goto_r0" },
  { c15, TK_SHOW_PARAM, "symbol_next_goto_r0" },
  { c15, TK_SHOW_PARAMS, "symbol_next_goto_r0" },
  { c15, TK_SHOW_STATS, "symbol_next_goto_r0" },
  { c15, TK_RESET_STATS, "symbol_next_goto_r0" },
  { c15, TK_SET_TIMEOUT, "symbol_next_goto_r0" },
  { c15, TK_SHOW_TIMEOUT, "symbol_next_goto_r0" },
  { c15, TK_HELP, "symbol_next_goto_r0" },
  { c15, TK_EF_SOLVE, "symbol_next_goto_r0" },
  { c15, TK_EXPORT_TO_DIMACS, "symbol_next_goto_r0" },
  { c15, TK_SHOW_IMPLICANT, "symbol_next_goto_r0" },
  { c15, TK_SHOW_UNSAT_CORE, "symbol_next_goto_r0" },
  { c15, TK_SHOW_UNSAT_ASSUMPTIONS, "symbol_next_goto_r0" },
  { c15, TK_SHOW_REDUCED_MODEL, "symbol_next_goto_r0" },
  { c15, TK_UPDATE, "symbol_next_goto_r0" },
  { c15, TK_FORALL, "symbol_next_goto_r0" },
  { c15, TK_EXISTS, "symbol_next_goto_r0" },
  { c15, TK_LAMBDA, "symbol_next_goto_r0" },
  { c15, TK_LET, "symbol_next_goto_r0" },
  { c15, TK_BOOL, "symbol_next_goto_r0" },
  { c15, TK_INT, "symbol_next_goto_r0" },
  { c15, TK_REAL, "symbol_next_goto_r0" },
  { c15, TK_BITVECTOR, "symbol_next_goto_r0" },
  { c15, TK_SCALAR, "symbol_next_goto_r0" },
  { c15, TK_TUPLE, "symbol_next_goto_r0" },
  { c15, TK_ARROW, "symbol_next_goto_r0" },
  { c15, TK_TRUE, "symbol_next_goto_r0" },
  { c15, TK_FALSE, "symbol_next_goto_r0" },
  { c15, TK_IF, "symbol_next_goto_r0" },
  { c15, TK_ITE, "symbol_next_goto_r0" },
  { c15, TK_EQ, "symbol_next_goto_r0" },
  { c15, TK_DISEQ, "symbol_next_goto_r0" },
  { c15, TK_DISTINCT, "symbol_next_goto_r0" },
  { c15, TK_OR, "symbol_next_goto_r0" },
  { c15, TK_AND, "symbol_next_goto_r0" },
  { c15, TK_NOT, "symbol_next_goto_r0" },
  { c15, TK_XOR, "symbol_next_goto_r0" },
  { c15, TK_IFF, "symbol_next_goto_r0" },
  { c15, TK_IMPLIES, "symbol_next_goto_r0" },
  { c15, TK_MK_TUPLE, "symbol_next_goto_r0" },
  { c15, TK_SELECT, "symbol_next_goto_r0" },
  { c15, TK_UPDATE_TUPLE, "symbol_next_goto_r0" },
  { c15, TK_ADD, "symbol_next_goto_r0" },
  { c15, TK_SUB, "symbol_next_goto_r0" },
  { c15, TK_MUL, "symbol_next_goto_r0" },
  { c15, TK_DIV, "symbol_next_goto_r0" },
  { c15, TK_POW, "symbol_next_goto_r0" },
  { c15, TK_LT, "symbol_next_goto_r0" },
  { c15, TK_LE, "symbol_next_goto_r0" },
  { c15, TK_GT, "symbol_next_goto_r0" },
  { c15, TK_GE, "symbol_next_goto_r0" },
  { c15, TK_MK_BV, "symbol_next_goto_r0" },
  { c15, TK_BV_ADD, "symbol_next_goto_r0" },
  { c15, TK_BV_SUB, "symbol_next_goto_r0" },
  { c15, TK_BV_MUL, "symbol_next_goto_r0" },
  { c15, TK_BV_NEG, "symbol_next_goto_r0" },
  { c15, TK_BV_POW, "symbol_next_goto_r0" },
  { c15, TK_BV_NOT, "symbol_next_goto_r0" },
  { c15, TK_BV_AND, "symbol_next_goto_r0" },
  { c15, TK_BV_OR, "symbol_next_goto_r0" },
  { c15, TK_BV_XOR, "symbol_next_goto_r0" },
  { c15, TK_BV_NAND, "symbol_next_goto_r0" },
  { c15, TK_BV_NOR, "symbol_next_goto_r0" },
  { c15, TK_BV_XNOR, "symbol_next_goto_r0" },
  { c15, TK_BV_SHIFT_LEFT0, "symbol_next_goto_r0" },
  { c15, TK_BV_SHIFT_LEFT1, "symbol_next_goto_r0" },
  { c15, TK_BV_SHIFT_RIGHT0, "symbol_next_goto_r0" },
  { c15, TK_BV_SHIFT_RIGHT1, "symbol_next_goto_r0" },
  { c15, TK_BV_ASHIFT_RIGHT, "symbol_next_goto_r0" },
  { c15, TK_BV_ROTATE_LEFT, "symbol_next_goto_r0" },
  { c15, TK_BV_ROTATE_RIGHT, "symbol_next_goto_r0" },
  { c15, TK_BV_EXTRACT, "symbol_next_goto_r0" },
  { c15, TK_BV_CONCAT, "symbol_next_goto_r0" },
  { c15, TK_BV_REPEAT, "symbol_next_goto_r0" },
  { c15, TK_BV_SIGN_EXTEND, "symbol_next_goto_r0" },
  { c15, TK_BV_ZERO_EXTEND, "symbol_next_goto_r0" },
  { c15, TK_BV_GE, "symbol_next_goto_r0" },
  { c15, TK_BV_GT, "symbol_next_goto_r0" },
  { c15, TK_BV_LE, "symbol_next_goto_r0" },
  { c15, TK_BV_LT, "symbol_next_goto_r0" },
  { c15, TK_BV_SGE, "symbol_next_goto_r0" },
  { c15, TK_BV_SGT, "symbol_next_goto_r0" },
  { c15, TK_BV_SLE, "symbol_next_goto_r0" },
  { c15, TK_BV_SLT, "symbol_next_goto_r0" },
  { c15, TK_BV_SHL, "symbol_next_goto_r0" },
  { c15, TK_BV_LSHR, "symbol_next_goto_r0" },
  { c15, TK_BV_ASHR, "symbol_next_goto_r0" },
  { c15, TK_BV_DIV, "symbol_next_goto_r0" },
  { c15, TK_BV_REM, "symbol_next_goto_r0" },
  { c15, TK_BV_SDIV, "symbol_next_goto_r0" },
  { c15, TK_BV_SREM, "symbol_next_goto_r0" },
  { c15, TK_BV_SMOD, "symbol_next_goto_r0" },
  { c15, TK_BV_REDOR, "symbol_next_goto_r0" },
  { c15, TK_BV_REDAND, "symbol_next_goto_r0" },
  { c15, TK_BV_COMP, "symbol_next_goto_r0" },
  { c15, TK_BOOL_TO_BV, "symbol_next_goto_r0" },
  { c15, TK_BIT, "symbol_next_goto_r0" },
  { c15, TK_FLOOR, "symbol_next_goto_r0" },
  { c15, TK_CEIL, "symbol_next_goto_r0" },
  { c15, TK_ABS, "symbol_next_goto_r0" },
  { c15, TK_IDIV, "symbol_next_goto_r0" },
  { c15, TK_MOD, "symbol_next_goto_r0" },
  { c15, TK_DIVIDES, "symbol_next_goto_r0" },
  { c15, TK_IS_INT, "symbol_next_goto_r0" },
  { c15, TK_SYMBOL, "symbol_next_goto_r0" },
  { c15, TK_STRING, "string_next_goto_r0" },
  { c15, TK_RP, "ret" },

  // list of assumptions
  { c16, TK_RP, "ret" },
  { c16, TK_SYMBOL, "symbol_next_goto_c16" },
  { c16, TK_LP, "next_goto_c17" },

  { c17, TK_NOT, "not_next_goto_c18" },
  { c17, DEFAULT_TOKEN, "error_not_expected" },

  { c18, TK_SYMBOL, "symbol_next_goto_c19" },
  { c18, DEFAULT_TOKEN, "error_symbol_expected" },

  { c19, TK_RP, "next_goto_c16" },
  { c19, DEFAULT_TOKEN, "error_rpar_expected" },

  { c20, TK_RP, "ret" },
  { c20, TK_SYMBOL, "symbol_next_goto_r0" },

  { td0, TK_INT, "int_return" },
  { td0, TK_REAL, "real_return" },
  { td0, TK_BOOL, "bool_return" },
  { td0, TK_SYMBOL, "typesymbol_return" },
  { td0, TK_LP, "next_goto_td1" },

  { td1, TK_SCALAR, "scalar_next_goto_td2" },
  { td1, TK_BITVECTOR, "bitvector_next_goto_t4" },
  { td1, TK_TUPLE, "tuple_next_push_t6_goto_t0" },
  { td1, TK_ARROW, "arrow_next_push_t6_push_t0_goto_t0" },

  { td2, TK_SYMBOL, "termname_next_goto_td3" },
  { td2, DEFAULT_TOKEN, "error_symbol_expected" },

  { td3, TK_RP, "ret" },
  { td3, TK_SYMBOL, "termname_next_goto_td3" },

  { t0, TK_INT, "int_return" },
  { t0, TK_REAL, "real_return" },
  { t0, TK_BOOL, "bool_return" },
  { t0, TK_SYMBOL, "typesymbol_return" },
  { t0, TK_LP, "next_goto_t1" },

  { t1, TK_BITVECTOR, "bitvector_next_goto_t4" },
  { t1, TK_TUPLE, "tuple_next_push_t6_goto_t0" },
  { t1, TK_ARROW, "arrow_next_push_t6_push_t0_goto_t0" },

  { t4, TK_NUM_RATIONAL, "rational_next_goto_r0" },
  { t4, DEFAULT_TOKEN, "error_rational_expected" },

  { t6, TK_RP, "ret" },
  { t6, DEFAULT_TOKEN, "push_t6_goto_t0" },

  { e0, TK_TRUE, "true_return" },
  { e0, TK_FALSE, "false_return" },
  { e0, TK_NUM_RATIONAL, "rational_return" },
  { e0, TK_NUM_FLOAT, "float_return" },
  { e0, TK_BV_CONSTANT, "bvbin_return" },
  { e0, TK_HEX_CONSTANT, "bvhex_return" },
  { e0, TK_SYMBOL, "termsymbol_return" },
  { e0, TK_LP, "next_goto_e1" },

  { e1, TK_IF, "if_next_push_e3_goto_e0" },
  { e1, TK_ITE, "if_next_push_e3_goto_e0" },
  { e1, TK_EQ, "eq_next_push_e3_goto_e0" },
  { e1, TK_DISEQ, "diseq_next_push_e3_goto_e0" },
  { e1, TK_DISTINCT, "distinct_next_push_e3_goto_e0" },
  { e1, TK_OR, "or_next_push_e3_goto_e0" },
  { e1, TK_AND, "and_next_push_e3_goto_e0" },
  { e1, TK_NOT, "not_next_push_e3_goto_e0" },
  { e1, TK_XOR, "xor_next_push_e3_goto_e0" },
  { e1, TK_IFF, "iff_next_push_e3_goto_e0" },
  { e1, TK_IMPLIES, "implies_next_push_e3_goto_e0" },
  { e1, TK_MK_TUPLE, "mk_tuple_next_push_e3_goto_e0" },
  { e1, TK_SELECT, "select_next_push_e3_goto_e0" },
  { e1, TK_UPDATE_TUPLE, "update_tuple_next_push_e3_goto_e0" },
  { e1, TK_ADD, "add_next_push_e3_goto_e0" },
  { e1, TK_SUB, "sub_next_push_e3_goto_e0" },
  { e1, TK_MUL, "mul_next_push_e3_goto_e0" },
  { e1, TK_DIV, "div_next_push_e3_goto_e0" },
  { e1, TK_POW, "pow_next_push_e3_goto_e0" },
  { e1, TK_LT, "lt_next_push_e3_goto_e0" },
  { e1, TK_LE, "le_next_push_e3_goto_e0" },
  { e1, TK_GT, "gt_next_push_e3_goto_e0" },
  { e1, TK_GE, "ge_next_push_e3_goto_e0" },
  { e1, TK_MK_BV, "mk_bv_next_push_e3_goto_e0" },
  { e1, TK_BV_ADD, "bv_add_next_push_e3_goto_e0" },
  { e1, TK_BV_SUB, "bv_sub_next_push_e3_goto_e0" },
  { e1, TK_BV_MUL, "bv_mul_next_push_e3_goto_e0" },
  { e1, TK_BV_NEG, "bv_neg_next_push_e3_goto_e0" },
  { e1, TK_BV_POW, "bv_pow_next_push_e3_goto_e0" },
  { e1, TK_BV_NOT, "bv_not_next_push_e3_goto_e0" },
  { e1, TK_BV_AND, "bv_and_next_push_e3_goto_e0" },
  { e1, TK_BV_OR, "bv_or_next_push_e3_goto_e0" },
  { e1, TK_BV_XOR, "bv_xor_next_push_e3_goto_e0" },
  { e1, TK_BV_NAND, "bv_nand_next_push_e3_goto_e0" },
  { e1, TK_BV_NOR, "bv_nor_next_push_e3_goto_e0" },
  { e1, TK_BV_XNOR, "bv_xnor_next_push_e3_goto_e0" },
  { e1, TK_BV_SHIFT_LEFT0, "bv_shift_left0_next_push_e3_goto_e0" },
  { e1, TK_BV_SHIFT_LEFT1, "bv_shift_left1_next_push_e3_goto_e0" },
  { e1, TK_BV_SHIFT_RIGHT0, "bv_shift_right0_next_push_e3_goto_e0" },
  { e1, TK_BV_SHIFT_RIGHT1, "bv_shift_right1_next_push_e3_goto_e0" },
  { e1, TK_BV_ASHIFT_RIGHT, "bv_ashift_right_next_push_e3_goto_e0" },
  { e1, TK_BV_ROTATE_LEFT, "bv_rotate_left_next_push_e3_goto_e0" },
  { e1, TK_BV_ROTATE_RIGHT, "bv_rotate_right_next_push_e3_goto_e0" },
  { e1, TK_BV_EXTRACT, "bv_extract_next_push_e3_goto_e0" },
  { e1, TK_BV_CONCAT, "bv_concat_next_push_e3_goto_e0" },
  { e1, TK_BV_REPEAT, "bv_repeat_next_push_e3_goto_e0" },
  { e1, TK_BV_SIGN_EXTEND, "bv_sign_extend_next_push_e3_goto_e0" },
  { e1, TK_BV_ZERO_EXTEND, "bv_zero_extend_next_push_e3_goto_e0" },
  { e1, TK_BV_GE, "bv_ge_next_push_e3_goto_e0" },
  { e1, TK_BV_GT, "bv_gt_next_push_e3_goto_e0" },
  { e1, TK_BV_LE, "bv_le_next_push_e3_goto_e0" },
  { e1, TK_BV_LT, "bv_lt_next_push_e3_goto_e0" },
  { e1, TK_BV_SGE, "bv_sge_next_push_e3_goto_e0" },
  { e1, TK_BV_SGT, "bv_sgt_next_push_e3_goto_e0" },
  { e1, TK_BV_SLE, "bv_sle_next_push_e3_goto_e0" },
  { e1, TK_BV_SLT, "bv_slt_next_push_e3_goto_e0" },
  { e1, TK_BV_SHL, "bv_shl_next_push_e3_goto_e0" },
  { e1, TK_BV_LSHR, "bv_lshr_next_push_e3_goto_e0" },
  { e1, TK_BV_ASHR, "bv_ashr_next_push_e3_goto_e0" },
  { e1, TK_BV_DIV, "bv_div_next_push_e3_goto_e0" },
  { e1, TK_BV_REM, "bv_rem_next_push_e3_goto_e0" },
  { e1, TK_BV_SDIV, "bv_sdiv_next_push_e3_goto_e0" },
  { e1, TK_BV_SREM, "bv_srem_next_push_e3_goto_e0" },
  { e1, TK_BV_SMOD, "bv_smod_next_push_e3_goto_e0" },
  { e1, TK_BV_REDOR, "bv_redor_next_push_e3_goto_e0" },
  { e1, TK_BV_REDAND, "bv_redand_next_push_e3_goto_e0" },
  { e1, TK_BV_COMP, "bv_comp_next_push_e3_goto_e0" },
  { e1, TK_BOOL_TO_BV, "bool_to_bv_next_push_e3_goto_e0" },
  { e1, TK_BIT, "bit_next_push_e3_goto_e0" },
  { e1, TK_FLOOR, "floor_next_push_e3_goto_e0" },
  { e1, TK_CEIL, "ceil_next_push_e3_goto_e0" },
  { e1, TK_ABS, "abs_next_push_e3_goto_e0" },
  { e1, TK_IDIV, "idiv_next_push_e3_goto_e0" },
  { e1, TK_MOD, "mod_next_push_e3_goto_e0" },
  { e1, TK_DIVIDES, "divides_next_push_e3_goto_e0" },
  { e1, TK_IS_INT, "is_int_next_push_e3_goto_e0" },

  { e1, TK_UPDATE, "update_next_push_e5_goto_e0" },
  { e1, TK_FORALL, "forall_next_goto_e10" },
  { e1, TK_EXISTS, "exists_next_goto_e10" },
  { e1, TK_LAMBDA, "lambda_next_goto_e10" },
  { e1, TK_LET, "let_next_goto_e15" },
  { e1, DEFAULT_TOKEN, "push_e3_push_e0_goto_e0" },

  { e3, TK_RP, "ret" },
  { e3, DEFAULT_TOKEN, "push_e3_goto_e0" },

  { e5, TK_LP, "next_push_e7_goto_e0" },
  { e5, DEFAULT_TOKEN, "error_lpar_expected" },

  { e7, TK_RP, "next_push_r0_goto_e0" },
  { e7, DEFAULT_TOKEN, "push_e7_goto_e0" },

  { e10, TK_LP, "next_goto_e11" },
  { e10, DEFAULT_TOKEN, "error_lpar_expected" },

  { e11, TK_SYMBOL, "e11_varname_next_goto_e12" },
  { e11, DEFAULT_TOKEN, "error_symbol_expected" },

  { e12, TK_COLON_COLON, "next_push_e14_goto_t0" },
  { e12, DEFAULT_TOKEN, "error_colon_colon_expected" },

  { e14, TK_RP, "e14_next_push_r0_goto_e0" },
  { e14, TK_SYMBOL, "e14_varname_next_goto_e12" },

  { e15, TK_LP, "bind_next_goto_e16" },
  { e15, DEFAULT_TOKEN, "error_lpar_expected" },

  { e16, TK_LP, "next_goto_e17" },
  { e16, DEFAULT_TOKEN, "error_lpar_expected" },

  { e17, TK_SYMBOL, "termname_next_push_e19_goto_e0" },
  { e17, DEFAULT_TOKEN, "error_symbol_expected" },

  { e19, TK_RP, "next_goto_e20" },
  { e19, DEFAULT_TOKEN, "error_rpar_expected" },

  { e20, TK_LP, "next_goto_e17" },
  { e20, TK_RP, "close_next_push_r0_goto_e0" },

  { r0, TK_RP, "ret" },
  { r0, DEFAULT_TOKEN, "error_rpar_expected" },

  { -1, -1, NULL },
};

#define NSTATES (e20+1)
#define NTOKENS (TK_ERROR+1)
#define DEFAULT_VALUE "error"
