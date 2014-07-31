/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "frontend/smt1/smt_lexer.h"

typedef enum state_s {
  an0, an1,
  bt0, bt1, bt2, bt3,
  s0, s1, s2, s3, s4, s5, s6, s7, s8,
  f0, f1, f3, f4, f5, f6, f7, f8, f9, f10, f11, 
  f14, f15, f16, f17, f19, f20, f21, f23, f24, f25, f26, f27,
  b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
  b11, b12, b13, b14, b15, b16, b17, b18, b19, 
  b20, b21, b22, b24, b25, b27
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
  // annotations
  next_goto_an1,
  return_notoken,
  next_goto_an0,

  // basic term or atom
  var_next_return,
  fvar_next_return,
  rational_next_return,
  float_next_return,
  bvbin_next_return,
  bvhex_next_return,
  true_next_return,
  false_next_return,
  bit0_next_return,
  bit1_next_return,
  next_goto_bt1,  // bvconst
  next_goto_bt2,  // [
  endbvconst_return,
  next_goto_bt3,  // rational
  next_return,    // ]

  // sort
  //  u_next_return,
  int_next_return,
  real_next_return,
  array1_next_return,
  array2_next_return,
  sortsymbol_next_return,
  next_goto_s1,  // BitVec
  next_goto_s4,  // Array
  next_goto_s2,  // [
  next_goto_s3,  // rational
  next_goto_s5,  // [
  array_return,
  next_goto_s6,  // rational
  next_goto_s7,
  next_goto_s8,  // rational
  bvarray_next_return,

  // annotated formula or term
  termsymbol_next_return,
  next_goto_f1,
  goto_bt0,

  // all simple function keywords:
  distinct_next_push_f3_goto_f0,
  eq_next_push_f3_goto_f0,
  not_next_push_f3_goto_f0,
  implies_next_push_f3_goto_f0,  
  if_then_else_next_push_f3_goto_f0,
  and_next_push_f3_goto_f0,
  or_next_push_f3_goto_f0,
  xor_next_push_f3_goto_f0,
  iff_next_push_f3_goto_f0,
  ite_next_push_f3_goto_f0,
  add_next_push_f3_goto_f0,
  sub_next_push_f3_goto_f0,
  mul_next_push_f3_goto_f0,
  div_next_push_f3_goto_f0,
  tilde_next_push_f3_goto_f0,
  lt_next_push_f3_goto_f0,
  le_next_push_f3_goto_f0,
  gt_next_push_f3_goto_f0,
  ge_next_push_f3_goto_f0,
  select_next_push_f3_goto_f0,
  store_next_push_f3_goto_f0,
  bvadd_next_push_f3_goto_f0,
  bvsub_next_push_f3_goto_f0,
  bvmul_next_push_f3_goto_f0,
  bvneg_next_push_f3_goto_f0,
  bvor_next_push_f3_goto_f0,
  bvand_next_push_f3_goto_f0,
  bvxor_next_push_f3_goto_f0,
  bvnot_next_push_f3_goto_f0,
  bvlt_next_push_f3_goto_f0,
  bvleq_next_push_f3_goto_f0,
  bvgt_next_push_f3_goto_f0,
  bvgeq_next_push_f3_goto_f0,
  bvslt_next_push_f3_goto_f0,
  bvsleq_next_push_f3_goto_f0,
  bvsgt_next_push_f3_goto_f0,
  bvsgeq_next_push_f3_goto_f0,
  concat_next_push_f3_goto_f0,
  shift_left0_next_push_f3_goto_f0,
  shift_right0_next_push_f3_goto_f0,
  shift_left1_next_push_f3_goto_f0,
  shift_right1_next_push_f3_goto_f0,
  bvudiv_next_push_f3_goto_f0,
  bvurem_next_push_f3_goto_f0,
  bvsdiv_next_push_f3_goto_f0,
  bvsrem_next_push_f3_goto_f0,
  bvsmod_next_push_f3_goto_f0,
  bvshl_next_push_f3_goto_f0,
  bvlshr_next_push_f3_goto_f0,
  bvashr_next_push_f3_goto_f0,
  bvnand_next_push_f3_goto_f0,
  bvnor_next_push_f3_goto_f0,
  bvxnor_next_push_f3_goto_f0,
  bvredor_next_push_f3_goto_f0,
  bvredand_next_push_f3_goto_f0,
  bvcomp_next_push_f3_goto_f0,
  bvult_next_push_f3_goto_f0,
  bvule_next_push_f3_goto_f0,
  bvugt_next_push_f3_goto_f0,
  bvuge_next_push_f3_goto_f0,
  bvsle_next_push_f3_goto_f0,
  bvsge_next_push_f3_goto_f0,

  symbol_next_goto_f4,
  extract_next_goto_f6,
  rotate_left_next_goto_f9,
  rotate_right_next_goto_f9,
  repeat_next_goto_f9,
  zero_extend_next_goto_f9,
  sign_extend_next_goto_f14,
  let_next_goto_f16,
  exists_next_goto_f20,
  forall_next_goto_f20,
  push_f5_goto_bt0,

  next_push_f26_goto_an1,
  push_f3_goto_f0,

  next_push_f27_goto_an1,
  applyfun_push_f3_goto_f0,

  next_return_noapply, // f27

  next_goto_f7,
  rational_next_goto_f8,
  next_goto_f10,
  rational_next_goto_f11,
  next_push_f26_push_an0_goto_f0,

  push_f15_goto_f0,
  rational_next_push_f26_goto_an0,

  next_goto_f17,
  var_next_push_f19_goto_f0,
  bind_next_push_f26_push_an0_goto_f0,

  next_goto_f21,
  var_next_push_f23_goto_s0,
  next_goto_f24,

  next_goto_f25,
  symbol_next_push_f26_goto_an0,
  push_f26_push_an0_goto_bt0,

  push_f26_push_an0_goto_f1,

  // benchmark
  next_goto_b1,
  next_goto_b2,
  benchmarkname_next_goto_b3,

  notes_next_goto_b4,
  status_next_goto_b5,
  assert_next_push_b6_goto_f0,
  logic_next_goto_b7,
  extrasorts_next_goto_b11,
  extrapreds_next_goto_b14,
  extrafuns_next_goto_b20,
  next_push_b3_goto_an1,
  end_benchmark_return,

  next_goto_b3,
  sat_next_goto_b3,
  unsat_next_goto_b3,
  unknown_next_goto_b3,

  eval_assert_goto_b3,

  logicname_next_goto_b8,
  next_goto_b9,
  goto_b3,
  rational_next_goto_b10,
  endlogic_next_goto_b3,

  next_goto_b12,
  sortsymbol_next_goto_b13,

  next_goto_b15,
  next_goto_b16,
  predsymbol_next_goto_b17,
  next_goto_b19,
  next_push_b18_goto_an1,
  push_b17_goto_s0,

  next_goto_b21,
  next_goto_b22,
  funsymbol_next_push_b24_goto_s0,
  next_goto_b25,
  next_push_b27_goto_an1,
  push_b24_goto_s0,

  error_rational_expected,
  error_rb_expected,
  error_lb_expected,
  error_colon_expected,
  error_attribute_expected,
  error_lp_expected,
  error_rp_expected,
  error_var_expected,
  error_benchmark_expected,
  error_symbol_expected,
  error_string_expected,
  error_status_expected,
  error,
};

static triple_t triples[] = {
  { an0, SMT_TK_ATTRIBUTE, "next_goto_an1" },
  { an0, SMT_TK_PAT, "next_goto_an1" },
  { an0, SMT_TK_NOPAT, "next_goto_an1" },
  { an0, DEFAULT_TOKEN, "return_notoken" },

  { an1, SMT_TK_ATTRIBUTE, "next_goto_an1" },
  { an1, SMT_TK_PAT, "next_goto_an1" },
  { an1, SMT_TK_NOPAT, "next_goto_an1" },
  { an1, SMT_TK_USER_VALUE, "next_goto_an0" },
  { an1, DEFAULT_TOKEN, "return_notoken" },

  { bt0, SMT_TK_VAR, "var_next_return" },
  { bt0, SMT_TK_FVAR, "fvar_next_return" },
  { bt0, SMT_TK_RATIONAL, "rational_next_return" },
  { bt0, SMT_TK_FLOAT, "float_next_return" },
  { bt0, SMT_TK_BV_BINCONSTANT, "bvbin_next_return" },
  { bt0, SMT_TK_BV_HEXCONSTANT, "bvhex_next_return" },
  { bt0, SMT_TK_TRUE, "true_next_return" },
  { bt0, SMT_TK_FALSE, "false_next_return" },
  { bt0, SMT_TK_BIT0, "bit0_next_return" },
  { bt0, SMT_TK_BIT1, "bit1_next_return" },
  { bt0, SMT_TK_BV_CONSTANT, "next_goto_bt1" },

  { bt1, SMT_TK_LB, "next_goto_bt2" },
  { bt1, DEFAULT_TOKEN, "endbvconst_return" },

  { bt2, SMT_TK_RATIONAL, "next_goto_bt3" },
  { bt2, DEFAULT_TOKEN, "error_rational_expected" },

  { bt3, SMT_TK_RB, "next_return" },
  { bt3, DEFAULT_TOKEN, "error_rb_expected" },

  // removed  { s0, SMT_TK_U, "u_next_return" },
  { s0, SMT_TK_INT, "int_next_return" },
  { s0, SMT_TK_REAL, "real_next_return" },
  { s0, SMT_TK_ARRAY1, "array1_next_return" },
  { s0, SMT_TK_ARRAY2, "array2_next_return" },
  { s0, SMT_TK_SYMBOL, "sortsymbol_next_return" },
  { s0, SMT_TK_BITVEC, "next_goto_s1" },
  { s0, SMT_TK_ARRAY, "next_goto_s4" },

  { s1, SMT_TK_LB, "next_goto_s2" },
  { s1, DEFAULT_TOKEN, "error_lb_expected" },

  { s2, SMT_TK_RATIONAL, "next_goto_s3" },
  { s2, DEFAULT_TOKEN, "error_rational_expected" },

  { s3, SMT_TK_RB, "next_return" },
  { s3, DEFAULT_TOKEN, "error_rb_expected" },

  { s4, SMT_TK_LB, "next_goto_s5" },
  { s4, DEFAULT_TOKEN, "array_return" },

  { s5, SMT_TK_RATIONAL, "next_goto_s6" },
  { s5, DEFAULT_TOKEN, "error_rational_expected" },

  { s6, SMT_TK_COLON, "next_goto_s7" },
  { s6, DEFAULT_TOKEN, "error_colon_expected" },

  { s7, SMT_TK_RATIONAL, "next_goto_s8" },
  { s7, DEFAULT_TOKEN, "error_rational_expected" },

  { s8, SMT_TK_RB, "bvarray_next_return" },
  { s8, DEFAULT_TOKEN, "error_rb_expected" },

  { f0, SMT_TK_SYMBOL, "termsymbol_next_return" },
  { f0, SMT_TK_LP, "next_goto_f1" },
  { f0, DEFAULT_TOKEN, "goto_bt0" },

  { f1, SMT_TK_DISTINCT, "distinct_next_push_f3_goto_f0", },
  { f1, SMT_TK_EQ, "eq_next_push_f3_goto_f0" },
  { f1, SMT_TK_NOT, "not_next_push_f3_goto_f0" },
  { f1, SMT_TK_IMPLIES, "implies_next_push_f3_goto_f0" },
  { f1, SMT_TK_IF_THEN_ELSE, "if_then_else_next_push_f3_goto_f0" },
  { f1, SMT_TK_AND, "and_next_push_f3_goto_f0" },
  { f1, SMT_TK_OR, "or_next_push_f3_goto_f0" },
  { f1, SMT_TK_XOR, "xor_next_push_f3_goto_f0" },
  { f1, SMT_TK_IFF, "iff_next_push_f3_goto_f0" },
  { f1, SMT_TK_ITE, "ite_next_push_f3_goto_f0" },
  { f1, SMT_TK_ADD, "add_next_push_f3_goto_f0" },
  { f1, SMT_TK_SUB, "sub_next_push_f3_goto_f0" },
  { f1, SMT_TK_MUL, "mul_next_push_f3_goto_f0" },
  { f1, SMT_TK_DIV, "div_next_push_f3_goto_f0" },
  { f1, SMT_TK_TILDE, "tilde_next_push_f3_goto_f0" },
  { f1, SMT_TK_LT, "lt_next_push_f3_goto_f0" },
  { f1, SMT_TK_LE, "le_next_push_f3_goto_f0" },
  { f1, SMT_TK_GT, "gt_next_push_f3_goto_f0" },
  { f1, SMT_TK_GE, "ge_next_push_f3_goto_f0" },
  { f1, SMT_TK_SELECT, "select_next_push_f3_goto_f0" },
  { f1, SMT_TK_STORE, "store_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVADD, "bvadd_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVSUB, "bvsub_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVMUL, "bvmul_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVNEG, "bvneg_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVOR, "bvor_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVAND, "bvand_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVXOR, "bvxor_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVNOT, "bvnot_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVLT, "bvlt_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVLEQ, "bvleq_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVGT, "bvgt_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVGEQ, "bvgeq_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVSLT, "bvslt_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVSLEQ, "bvsleq_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVSGT, "bvsgt_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVSGEQ, "bvsgeq_next_push_f3_goto_f0" },
  { f1, SMT_TK_CONCAT, "concat_next_push_f3_goto_f0" },
  { f1, SMT_TK_SHIFT_LEFT0, "shift_left0_next_push_f3_goto_f0" },
  { f1, SMT_TK_SHIFT_RIGHT0, "shift_right0_next_push_f3_goto_f0" },
  { f1, SMT_TK_SHIFT_LEFT1, "shift_left1_next_push_f3_goto_f0" },
  { f1, SMT_TK_SHIFT_RIGHT1, "shift_right1_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVUDIV, "bvudiv_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVUREM, "bvurem_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVSDIV, "bvsdiv_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVSREM, "bvsrem_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVSMOD, "bvsmod_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVSHL, "bvshl_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVLSHR, "bvlshr_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVASHR, "bvashr_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVNAND, "bvnand_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVNOR, "bvnor_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVXNOR, "bvxnor_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVREDOR, "bvredor_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVREDAND, "bvredand_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVCOMP, "bvcomp_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVULT, "bvult_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVULE, "bvule_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVUGT, "bvugt_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVUGE, "bvuge_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVSLE, "bvsle_next_push_f3_goto_f0" },
  { f1, SMT_TK_BVSGE, "bvsge_next_push_f3_goto_f0" },
  { f1, SMT_TK_SYMBOL, "symbol_next_goto_f4" },
  { f1, SMT_TK_EXTRACT, "extract_next_goto_f6" },
  { f1, SMT_TK_ROTATE_LEFT, "rotate_left_next_goto_f9" },
  { f1, SMT_TK_ROTATE_RIGHT, "rotate_right_next_goto_f9" },
  { f1, SMT_TK_REPEAT, "repeat_next_goto_f9" },
  { f1, SMT_TK_ZERO_EXTEND, "zero_extend_next_goto_f9" },
  { f1, SMT_TK_SIGN_EXTEND, "sign_extend_next_goto_f14" },
  { f1, SMT_TK_LET, "let_next_goto_f16" },
  { f1, SMT_TK_FLET, "let_next_goto_f16" },
  { f1, SMT_TK_EXISTS, "exists_next_goto_f20" },
  { f1, SMT_TK_FORALL, "forall_next_goto_f20" },
  { f1, DEFAULT_TOKEN, "push_f5_goto_bt0" },

  { f3, SMT_TK_RP, "next_return" },
  { f3, SMT_TK_ATTRIBUTE, "next_push_f26_goto_an1" },
  { f3, SMT_TK_PAT, "next_push_f26_goto_an1" },
  { f3, SMT_TK_NOPAT, "next_push_f26_goto_an1" },
  { f3, DEFAULT_TOKEN, "push_f3_goto_f0" },

  { f4, SMT_TK_ATTRIBUTE, "next_push_f27_goto_an1" },
  { f4, SMT_TK_PAT, "next_push_f27_goto_an1" },
  { f4, SMT_TK_NOPAT, "next_push_f27_goto_an1" },
  { f4, DEFAULT_TOKEN, "applyfun_push_f3_goto_f0" },

  { f5, SMT_TK_ATTRIBUTE, "next_push_f27_goto_an1" },
  { f5, SMT_TK_PAT, "next_push_f27_goto_an1" },
  { f5, SMT_TK_NOPAT, "next_push_f27_goto_an1" },
  { f5, DEFAULT_TOKEN, "error_attribute_expected" },

  { f6, SMT_TK_LB, "next_goto_f7" },
  { f6, DEFAULT_TOKEN, "error_lb_expected" },

  { f7, SMT_TK_RATIONAL, "rational_next_goto_f8" },
  { f7, DEFAULT_TOKEN, "error_rational_expected" },

  { f8, SMT_TK_COLON, "next_goto_f10" },
  { f8, DEFAULT_TOKEN, "error_colon_expected" },

  { f9, SMT_TK_LB, "next_goto_f10" },
  { f9, DEFAULT_TOKEN, "error_lb_expected" },

  { f10, SMT_TK_RATIONAL, "rational_next_goto_f11" },
  { f10, DEFAULT_TOKEN, "error_rational_expected" },

  { f11, SMT_TK_RB, "next_push_f26_push_an0_goto_f0" },
  { f11, DEFAULT_TOKEN, "error_rb_expected" },

  { f14, SMT_TK_LB, "next_goto_f10" },
  { f14, DEFAULT_TOKEN, "push_f15_goto_f0" },

  { f15, SMT_TK_RATIONAL, "rational_next_push_f26_goto_an0" },
  { f15, DEFAULT_TOKEN, "error_rational_expected" },

  { f16, SMT_TK_LP, "next_goto_f17" },
  { f16, DEFAULT_TOKEN, "error_lp_expected" },

  { f17, SMT_TK_VAR, "var_next_push_f19_goto_f0" },
  { f17, SMT_TK_FVAR, "var_next_push_f19_goto_f0" },
  { f17, DEFAULT_TOKEN, "error_var_expected" },
  
  { f19, SMT_TK_RP, "bind_next_push_f26_push_an0_goto_f0" },
  { f19, DEFAULT_TOKEN, "error_rp_expected" },

  { f20, SMT_TK_LP, "next_goto_f21" },
  { f20, DEFAULT_TOKEN, "error_lp_expected" },

  { f21, SMT_TK_VAR, "var_next_push_f23_goto_s0" },
  { f21, DEFAULT_TOKEN, "error_var_expected" },

  { f23, SMT_TK_RP, "next_goto_f24" },
  { f23, DEFAULT_TOKEN, "error_rp_expected" },

  { f24, SMT_TK_LP, "next_goto_f25" },
  { f24, SMT_TK_SYMBOL, "symbol_next_push_f26_goto_an0" },
  { f24, DEFAULT_TOKEN, "push_f26_push_an0_goto_bt0" },

  { f25, SMT_TK_VAR, "var_next_push_f23_goto_s0" },
  { f25, DEFAULT_TOKEN, "push_f26_push_an0_goto_f1" },

  { f26, SMT_TK_RP, "next_return" },
  { f26, DEFAULT_TOKEN, "error_rp_expected" },

  { f27, SMT_TK_RP, "next_return_noapply" },
  { f27, DEFAULT_TOKEN, "error_rp_expected" },

  // benchmark
  { b0, SMT_TK_LP, "next_goto_b1" },
  { b0, DEFAULT_TOKEN, "error_lp_expected" },

  { b1, SMT_TK_BENCHMARK, "next_goto_b2" },
  { b1, DEFAULT_TOKEN, "error_benchmark_expected" },

  { b2, SMT_TK_SYMBOL, "benchmarkname_next_goto_b3" },
  { b2, DEFAULT_TOKEN, "error_symbol_expected" },

  { b3, SMT_TK_NOTES, "notes_next_goto_b4" },
  { b3, SMT_TK_STATUS, "status_next_goto_b5" },
  { b3, SMT_TK_ASSUMPTION, "assert_next_push_b6_goto_f0" },
  { b3, SMT_TK_FORMULA, "assert_next_push_b6_goto_f0" },
  { b3, SMT_TK_LOGIC, "logic_next_goto_b7" },
  { b3, SMT_TK_EXTRASORTS, "extrasorts_next_goto_b11" },
  { b3, SMT_TK_EXTRAPREDS, "extrapreds_next_goto_b14" },
  { b3, SMT_TK_EXTRAFUNS, "extrafuns_next_goto_b20" },
  { b3, SMT_TK_ATTRIBUTE, "next_push_b3_goto_an1" },
  { b3, SMT_TK_PAT, "next_push_b3_goto_an1" },
  { b3, SMT_TK_NOPAT, "next_push_b3_goto_an1" },
  { b3, SMT_TK_RP, "end_benchmark_return" },

  { b4, SMT_TK_STRING, "next_goto_b3" },
  { b4, DEFAULT_TOKEN, "error_string_expected" },

  { b5, SMT_TK_SAT, "sat_next_goto_b3" },
  { b5, SMT_TK_UNSAT, "unsat_next_goto_b3" },
  { b5, SMT_TK_UNKNOWN, "unknown_next_goto_b3" },
  { b5, DEFAULT_TOKEN, "error_status_expected" },

  { b6, DEFAULT_TOKEN, "eval_assert_goto_b3" },

  { b7, SMT_TK_SYMBOL, "logicname_next_goto_b8" },
  { b7, DEFAULT_TOKEN, "error_symbol_expected" },

  { b8, SMT_TK_LB, "next_goto_b9" },
  { b8, DEFAULT_TOKEN, "goto_b3" },

  { b9, SMT_TK_RATIONAL, "rational_next_goto_b10" },
  { b9, DEFAULT_TOKEN, "error_rational_expected" },

  { b10, SMT_TK_RB, "endlogic_next_goto_b3" },
  { b10, DEFAULT_TOKEN, "error_rb_expected" },

  { b11, SMT_TK_LP, "next_goto_b12" },
  { b11, DEFAULT_TOKEN, "error_lp_expected" },

  { b12, SMT_TK_SYMBOL, "sortsymbol_next_goto_b13" },
  { b12, DEFAULT_TOKEN, "error_symbol_expected" },

  { b13, SMT_TK_RP, "next_goto_b3" },
  { b13, SMT_TK_SYMBOL, "sortsymbol_next_goto_b13" },

  { b14, SMT_TK_LP, "next_goto_b15" },
  { b14, DEFAULT_TOKEN, "error_lp_expected" },

  { b15, SMT_TK_LP, "next_goto_b16" },
  { b16, SMT_TK_SYMBOL, "predsymbol_next_goto_b17" },

  { b17, SMT_TK_RP, "next_goto_b19" },
  { b17, SMT_TK_ATTRIBUTE, "next_push_b18_goto_an1" },
  { b17, SMT_TK_PAT, "next_push_b18_goto_an1" },
  { b17, SMT_TK_NOPAT, "next_push_b18_goto_an1" },
  { b17, DEFAULT_TOKEN, "push_b17_goto_s0" },

  { b18, SMT_TK_RP, "next_goto_b19" },
  { b18, DEFAULT_TOKEN, "error_rp_expected" },

  { b19, SMT_TK_LP, "next_goto_b16" },
  { b19, SMT_TK_RP, "next_goto_b3" },

  { b20, SMT_TK_LP, "next_goto_b21" },
  { b20, DEFAULT_TOKEN, "error_lp_expected" },

  { b21, SMT_TK_LP, "next_goto_b22" },
  { b21, DEFAULT_TOKEN, "error_lp_expected" },

  { b22, SMT_TK_SYMBOL, "funsymbol_next_push_b24_goto_s0" },
  { b22, DEFAULT_TOKEN, "error_symbol_expected" },

  { b24, SMT_TK_RP, "next_goto_b25" },
  { b24, SMT_TK_ATTRIBUTE, "next_push_b27_goto_an1" },
  { b24, SMT_TK_PAT, "next_push_b27_goto_an1" },
  { b24, SMT_TK_NOPAT, "next_push_b27_goto_an1" },
  { b24, DEFAULT_TOKEN, "push_b24_goto_s0" },

  { b25, SMT_TK_LP, "next_goto_b22" },
  { b25, SMT_TK_RP, "next_goto_b3" },

  { b27, SMT_TK_RP, "next_goto_b25" },
  { b27, DEFAULT_TOKEN, "error_rp_expected" },

  { -1, -1, NULL },
};

#define NSTATES (b27+1)
#define NTOKENS (SMT_TK_ERROR+1)
#define DEFAULT_VALUE "error"
