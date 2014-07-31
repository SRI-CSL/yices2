/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdint.h>

#include "frontend/smt1/smt_parse_tables.h"
#include "frontend/smt1/smt_lexer.h"

static action_t get_action(state_t s, token_t tk) {
  int32_t i;

  i = base[s] + tk;
  if (check[i] == s) {
    return value[i];
  } else {
    return default_value[s];
  }
}

static char* state2string[] = {
  "an0", "an1",
  "bt0", "bt1", "bt2", "bt3",
  "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8",
  "f0", "f1", "f3", "f4", "f5", "f6", "f7", "f8", "f9", "f10", "f11",
  "f14", "f15", "f16", "f17", "f19", "f20", "f21", "f23", "f24", "f25", "f26", "f27",
  "b0", "b1", "b2", "b3", "b4", "b5", "b6", "b7", "b8", "b9", "b10",
  "b11", "b12", "b13", "b14", "b15", "b16", "b17", "b18", "b19",
  "b20", "b21", "b22", "b24", "b25", "b27",
};

static char* action2string[] = {
  "next_goto_an1",
  "return_notoken",
  "next_goto_an0",
  "var_next_return",
  "fvar_next_return",
  "rational_next_return",
  "float_next_return",
  "bvbin_next_return",
  "bvhex_next_return",
  "true_next_return",
  "false_next_return",
  "bit0_next_return",
  "bit1_next_return",
  "next_goto_bt1",
  "next_goto_bt2",
  "endbvconst_return",
  "next_goto_bt3",
  "next_return",
  "int_next_return",
  "real_next_return",
  "array1_next_return",
  "array2_next_return",
  "sortsymbol_next_return",
  "next_goto_s1",
  "next_goto_s4",
  "next_goto_s2",
  "next_goto_s3",
  "next_goto_s5",
  "array_return",
  "next_goto_s6",
  "next_goto_s7",
  "next_goto_s8",
  "bvarray_next_return",
  "termsymbol_next_return",
  "next_goto_f1",
  "goto_bt0",
  "distinct_next_push_f3_goto_f0",
  "eq_next_push_f3_goto_f0",
  "not_next_push_f3_goto_f0",
  "implies_next_push_f3_goto_f0",
  "if_then_else_next_push_f3_goto_f0",
  "and_next_push_f3_goto_f0",
  "or_next_push_f3_goto_f0",
  "xor_next_push_f3_goto_f0",
  "iff_next_push_f3_goto_f0",
  "ite_next_push_f3_goto_f0",
  "add_next_push_f3_goto_f0",
  "sub_next_push_f3_goto_f0",
  "mul_next_push_f3_goto_f0",
  "div_next_push_f3_goto_f0",
  "tilde_next_push_f3_goto_f0",
  "lt_next_push_f3_goto_f0",
  "le_next_push_f3_goto_f0",
  "gt_next_push_f3_goto_f0",
  "ge_next_push_f3_goto_f0",
  "select_next_push_f3_goto_f0",
  "store_next_push_f3_goto_f0",
  "bvadd_next_push_f3_goto_f0",
  "bvsub_next_push_f3_goto_f0",
  "bvmul_next_push_f3_goto_f0",
  "bvneg_next_push_f3_goto_f0",
  "bvor_next_push_f3_goto_f0",
  "bvand_next_push_f3_goto_f0",
  "bvxor_next_push_f3_goto_f0",
  "bvnot_next_push_f3_goto_f0",
  "bvlt_next_push_f3_goto_f0",
  "bvleq_next_push_f3_goto_f0",
  "bvgt_next_push_f3_goto_f0",
  "bvgeq_next_push_f3_goto_f0",
  "bvslt_next_push_f3_goto_f0",
  "bvsleq_next_push_f3_goto_f0",
  "bvsgt_next_push_f3_goto_f0",
  "bvsgeq_next_push_f3_goto_f0",
  "concat_next_push_f3_goto_f0",
  "shift_left0_next_push_f3_goto_f0",
  "shift_right0_next_push_f3_goto_f0",
  "shift_left1_next_push_f3_goto_f0",
  "shift_right1_next_push_f3_goto_f0",
  "bvudiv_next_push_f3_goto_f0",
  "bvurem_next_push_f3_goto_f0",
  "bvsdiv_next_push_f3_goto_f0",
  "bvsrem_next_push_f3_goto_f0",
  "bvsmod_next_push_f3_goto_f0",
  "bvshl_next_push_f3_goto_f0",
  "bvlshr_next_push_f3_goto_f0",
  "bvashr_next_push_f3_goto_f0",
  "bvnand_next_push_f3_goto_f0",
  "bvnor_next_push_f3_goto_f0",
  "bvxnor_next_push_f3_goto_f0",
  "bvredor_next_push_f3_goto_f0",
  "bvredand_next_push_f3_goto_f0",
  "bvcomp_next_push_f3_goto_f0",
  "bvult_next_push_f3_goto_f0",
  "bvule_next_push_f3_goto_f0",
  "bvugt_next_push_f3_goto_f0",
  "bvuge_next_push_f3_goto_f0",
  "bvsle_next_push_f3_goto_f0",
  "bvsge_next_push_f3_goto_f0",
  "symbol_next_goto_f4",
  "extract_next_goto_f6",
  "rotate_left_next_goto_f9",
  "rotate_right_next_goto_f9",
  "repeat_next_goto_f9",
  "zero_extend_next_goto_f9",
  "sign_extend_next_goto_f14",
  "let_next_goto_f16",
  "exists_next_goto_f20",
  "forall_next_goto_f20",
  "push_f5_goto_bt0",
  "next_push_f26_goto_an1",
  "push_f3_goto_f0",
  "next_push_f27_goto_an1",
  "applyfun_push_f3_goto_f0",
  "next_return_noapply",
  "next_goto_f7",
  "rational_next_goto_f8",
  "next_goto_f10",
  "rational_next_goto_f11",
  "next_push_f26_push_an0_goto_f0",
  "push_f15_goto_f0",
  "rational_next_push_f26_push_an0_goto_f0",
  "next_goto_f17",
  "var_next_push_f19_goto_f0",
  "bind_next_push_f26_push_an0_goto_f0",
  "next_goto_f21",
  "var_next_push_f23_goto_s0",
  "next_goto_f24",
  "next_goto_f25",
  "symbol_next_push_f26_goto_an0",
  "push_f26_push_an0_goto_bt0",
  "push_f26_push_an0_goto_f1",
  "next_goto_b1",
  "next_goto_b2",
  "benchmarkname_next_goto_b3",
  "notes_next_goto_b4",
  "status_next_goto_b5",
  "assert_next_push_b6_goto_f0",
  "logic_next_goto_b7",
  "extrasorts_next_goto_b11",
  "extrapreds_next_goto_b14",
  "extrafuns_next_goto_b20",
  "next_push_b3_goto_an1",
  "end_benchmark_return",
  "next_goto_b3",
  "sat_next_goto_b3",
  "unsat_next_goto_b3",
  "unknown_next_goto_b3",
  "eval_assert_goto_b3",
  "logicname_next_goto_b8",
  "next_goto_b9",
  "goto_b3",
  "rational_next_goto_b10",
  "endlogic_next_goto_b3",
  "next_goto_b12",
  "sortsymbol_next_goto_b13",
  "next_goto_b15",
  "next_goto_b16",
  "predsymbol_next_goto_b17",
  "next_goto_b19",
  "next_push_b18_goto_an1",
  "push_b17_goto_s0",
  "next_goto_b21",
  "next_goto_b22",
  "funsymbol_next_push_b24_goto_s0",
  "next_goto_b25",
  "next_push_b27_goto_an1",
  "push_b24_goto_s0",
  "error_rational_expected",
  "error_rb_expected",
  "error_lb_expected",
  "error_colon_expected",
  "error_attribute_expected",
  "error_lp_expected",
  "error_rp_expected",
  "error_var_expected",
  "error_benchmark_expected",
  "error_symbol_expected",
  "error_string_expected",
  "error_status_expected",
  "error",
};


int main() {
  int32_t s, tk;
  lexer_t lex;

  init_smt_stdin_lexer(&lex);

  /*
   * NOTE: Clang (version 3.2) gives the following warning for s<NSTATES:
   *
   *    comparison of constant 64 with expression of type 'state_t'
   *    (aka 'enum state_s') is always true.
   *
   * It gives no warning for tk<NUM_SMT_TOKENS.
   *
   * I've changed the declaration of s: it used to be 'state_t s'
   * instead of 'int32_t s'
   */
  for (s=0; s<NSTATES; s++) {
    printf("Source state %s\n", state2string[s]);
    for (tk=SMT_TK_LP; tk<NUM_SMT_TOKENS; tk++) {
      printf("   %20s     %s\n", smt_token_to_string(tk), action2string[get_action(s, tk)]);
    }
    printf("\n");
  }

  close_lexer(&lex);

  return 0;
}
