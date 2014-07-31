/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdint.h>

#include "frontend/yices/yices_parse_tables.h"
#include "frontend/yices/yices_lexer.h"

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
 * States
 */
static const char* state2string[] = {
  "r0", "c0", "c1", "c2", "c3", "c6", "c7", "c9", "c10", "c11", "c12", "c13", "c14",
  "td0", "td1", "td2", "td3", "t0", "t1", "t4", "t6",
  "e0", "e1", "e3", "e5", "e7", "e10", "e11", "e12",
  "e14", "e15", "e16", "e17", "e19", "e20",
};


/*
 * Action codes
 */
static const char* action2string[] = {
  "next_goto_c1",
  "empty_command",
  "exit_next_goto_r0",
  "check_next_goto_r0",
  "push_next_goto_r0",
  "pop_next_goto_r0",
  "reset_next_goto_r0",
  "dump_context_next_goto_r0",
  "echo_next_goto_c3",
  "include_next_goto_c3",
  "assert_next_push_r0_goto_e0",
  "deftype_next_goto_c2",
  "defterm_next_goto_c6",
  "showmodel_next_goto_r0",
  "eval_next_push_r0_goto_e0",
  "setparam_next_goto_c11",
  "showparam_next_goto_c13",
  "showparams_next_goto_r0",
  "showstats_next_goto_r0",
  "resetstats_next_goto_r0",
  "showtimeout_next_goto_r0",
  "settimeout_next_goto_c14",
  "typename_next_goto_c10",
  "string_next_goto_r0",
  "termname_next_goto_c7",
  "next_push_c9_goto_t0",
  "symbol_next_goto_c12",
  "true_next_goto_r0",
  "false_next_goto_r0",
  "float_next_goto_r0",
  "symbol_next_goto_r0",
  "ret",
  "push_r0_goto_e0",
  "push_r0_goto_td0",
  "int_return",
  "real_return",
  "bool_return",
  "typesymbol_return",
  "next_goto_td1",
  "scalar_next_goto_td2",
  "bitvector_next_goto_t4",
  "tuple_next_push_t6_goto_t0",
  "arrow_next_push_t6_push_t0_goto_t0",
  "termname_next_goto_td3",
  "next_goto_t1",
  "rational_next_goto_r0",
  "push_t6_goto_t0",
  "true_return",
  "false_return",
  "rational_return",
  "float_return",
  "bvbin_return",
  "bvhex_return",
  "termsymbol_return",
  "next_goto_e1",
  "if_next_push_e3_goto_e0",
  "eq_next_push_e3_goto_e0",
  "diseq_next_push_e3_goto_e0",
  "distinct_next_push_e3_goto_e0",
  "or_next_push_e3_goto_e0",
  "and_next_push_e3_goto_e0",
  "not_next_push_e3_goto_e0",
  "xor_next_push_e3_goto_e0",
  "iff_next_push_e3_goto_e0",
  "implies_next_push_e3_goto_e0",
  "mk_tuple_next_push_e3_goto_e0",
  "select_next_push_e3_goto_e0",
  "update_tuple_next_push_e3_goto_e0",
  "add_next_push_e3_goto_e0",
  "sub_next_push_e3_goto_e0",
  "mul_next_push_e3_goto_e0",
  "div_next_push_e3_goto_e0",
  "pow_next_push_e3_goto_e0",
  "lt_next_push_e3_goto_e0",
  "le_next_push_e3_goto_e0",
  "gt_next_push_e3_goto_e0",
  "ge_next_push_e3_goto_e0",
  "mk_bv_next_push_e3_goto_e0",
  "bv_add_next_push_e3_goto_e0",
  "bv_sub_next_push_e3_goto_e0",
  "bv_mul_next_push_e3_goto_e0",
  "bv_neg_next_push_e3_goto_e0",
  "bv_pow_next_push_e3_goto_e0",
  "bv_not_next_push_e3_goto_e0",
  "bv_and_next_push_e3_goto_e0",
  "bv_or_next_push_e3_goto_e0",
  "bv_xor_next_push_e3_goto_e0",
  "bv_nand_next_push_e3_goto_e0",
  "bv_nor_next_push_e3_goto_e0",
  "bv_xnor_next_push_e3_goto_e0",
  "bv_shift_left0_next_push_e3_goto_e0",
  "bv_shift_left1_next_push_e3_goto_e0",
  "bv_shift_right0_next_push_e3_goto_e0",
  "bv_shift_right1_next_push_e3_goto_e0",
  "bv_ashift_right_next_push_e3_goto_e0",
  "bv_rotate_left_next_push_e3_goto_e0",
  "bv_rotate_right_next_push_e3_goto_e0",
  "bv_extract_next_push_e3_goto_e0",
  "bv_concat_next_push_e3_goto_e0",
  "bv_repeat_next_push_e3_goto_e0",
  "bv_sign_extend_next_push_e3_goto_e0",
  "bv_zero_extend_next_push_e3_goto_e0",
  "bv_ge_next_push_e3_goto_e0",
  "bv_gt_next_push_e3_goto_e0",
  "bv_le_next_push_e3_goto_e0",
  "bv_lt_next_push_e3_goto_e0",
  "bv_sge_next_push_e3_goto_e0",
  "bv_sgt_next_push_e3_goto_e0",
  "bv_sle_next_push_e3_goto_e0",
  "bv_slt_next_push_e3_goto_e0",
  "bv_shl_next_push_e3_goto_e0",
  "bv_lshr_next_push_e3_goto_e0",
  "bv_ashr_next_push_e3_goto_e0",
  "bv_div_next_push_e3_goto_e0",
  "bv_rem_next_push_e3_goto_e0",
  "bv_sdiv_next_push_e3_goto_e0",
  "bv_srem_next_push_e3_goto_e0",
  "bv_smod_next_push_e3_goto_e0",
  "bv_redor_next_push_e3_goto_e0",
  "bv_redand_next_push_e3_goto_e0",
  "bv_comp_next_push_e3_goto_e0",
  "update_next_push_e5_goto_e0",
  "forall_next_goto_e10",
  "exists_next_goto_e10",
  "lambda_next_goto_e10",
  "let_next_goto_e15",
  "push_e3_push_e0_goto_e0",
  "push_e3_goto_e0",
  "next_push_e7_goto_e0",
  "next_push_r0_goto_e0",
  "push_e7_goto_e0",
  "next_goto_e11",
  "e11_varname_next_goto_e12",
  "next_push_e14_goto_t0",
  "e14_varname_next_goto_e12",
  "e14_next_push_r0_goto_e0",
  "next_goto_e16",
  "next_goto_e17",
  "termname_next_push_e19_goto_e0",
  "next_goto_e20",
  "error_lpar_expected",
  "error_symbol_expected",
  "error_string_expected",
  "error_colon_colon_expected",
  "error_rational_expected",
  "error_rpar_expected",
  "error",
};


int main() {
  state_t s;
  token_t tk;
  lexer_t lex;
  char *c0;
  const char *c1;

  init_yices_stdin_lexer(&lex);

  for (s=0; s<NSTATES; s++) {
    printf("Source state %s\n", state2string[s]);
    for (tk=TK_DEFINE_TYPE; tk<NUM_YICES_TOKENS; tk++) {
      c0 = yices_token_to_string(tk);
      c1 = action2string[get_action(s, tk)];
      printf("   %20s     %s\n", c0, c1);
    }
    printf("\n");
  }

  close_lexer(&lex);

  return 0;
}
