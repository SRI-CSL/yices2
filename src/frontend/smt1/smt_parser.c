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
 * Parser for benchmarks in the SMT-LIB language.
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <stdio.h>
#include <setjmp.h>
#include <string.h>
#include <inttypes.h>

#include "api/yices_extensions.h"
#include "frontend/smt1/smt_lexer.h"
#include "frontend/smt1/smt_parse_tables.h"
#include "frontend/smt1/smt_parser.h"
#include "parser_utils/term_stack_error.h"
#include "utils/refcount_strings.h"

#include "yices.h"


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
 * Print a message on a syntax error
 * - lex = the lexer
 * - expected_token = what was expected or -1
 */
static void syntax_error(lexer_t *lex, int32_t expected_token) {
  smt_token_t tk;
  reader_t *rd;

  tk = current_token(lex);
  rd = &lex->reader;

  if (rd->name != NULL) {
    fprintf(stderr, "%s: ", rd->name);
  }

  switch (tk) {
  case SMT_TK_OPEN_STRING:
    fprintf(stderr, "missing string terminator \" (line %"PRId32", column %"PRId32")\n",
            rd->line, rd->column);
    return;
  case SMT_TK_OPEN_USER_VAL:
    fprintf(stderr, "missing user-value terminator } (line %"PRId32", column %"PRId32")\n",
            rd->line, rd->column);
    return;
  case SMT_TK_INVALID_NUMBER:
    fprintf(stderr, "invalid number %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    return;
  case SMT_TK_ZERO_DIVISOR:
    fprintf(stderr, "zero divisor in constant %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    return;
  case SMT_TK_ERROR:
    fprintf(stderr, "invalid token %s (line %"PRId32", column %"PRId32")\n",
            tkval(lex), lex->tk_line, lex->tk_column);
    return;

  default:
    switch(expected_token) {
    case SMT_TK_RB:
    case SMT_TK_LB:
    case SMT_TK_COLON:
    case SMT_TK_LP:
    case SMT_TK_RP:
    case SMT_TK_VAR:
    case SMT_TK_BENCHMARK:
    case SMT_TK_SYMBOL:
    case SMT_TK_STRING:
    case SMT_TK_ATTRIBUTE:
      fprintf(stderr, "syntax error (line %"PRId32", column %"PRId32"): %s expected\n",
              lex->tk_line, lex->tk_column, smt_token_to_string(expected_token));
      break;

    case SMT_TK_STATUS:
      fprintf(stderr, "syntax error (line %"PRId32", column %"PRId32"): status expected\n",
              lex->tk_line, lex->tk_column);
      break;

    case SMT_TK_RATIONAL:
      fprintf(stderr, "syntax error (line %"PRId32", column %"PRId32"): number expected\n",
              lex->tk_line, lex->tk_column);
      break;

    default:
      fprintf(stderr, "syntax error (line %"PRId32", column %"PRId32")\n",
              lex->tk_line, lex->tk_column);
      break;
    }
  }
}



/*********************************
 *  PREDEFINED TERMS AND TYPES   *
 ********************************/

/*
 * Warning: yices-1.0.xx incorrectly maps Array1 and Array to [int -> int]
 * New types added for smt2008: Index, Element, Array for QF_AX
 *
 * In smt2008, the keyword "Array" may denote either arrays of type [int -> int]
 * or arrays of type [index -> element], depending on the theory.
 * HACK: to deal with this, we assign the built-in type array to either int_array or
 * ax_array, depending on the logic.
 */
typedef struct builtins_s {
  // types for QF_UF
  type_t utype;  // uninterpreted type

  // types for QF_AX
  type_t index_type; // uninterpreted (for QF_AX)
  type_t elem_type;  // uninterpreted (for QF_AX)
  type_t ax_array;   // [index -> elem]

  // types for QF_AUFIDL/QF_AUFLIA/QF_ALIA
  type_t int_array;  // [int -> int]
  type_t array1; // [int -> real]
  type_t array2; // [int -> array1]

  // the array type, dependent on the logic
  type_t array;

  // bitvector constants
  term_t bit0;   // 0b0
  term_t bit1;   // 0b1

} builtins_t;



/*
 * Initialize all these:
 * - b->array is initialized to b->int_array.
 * - this is changed by the parser after it sees "QF_AX"
 */
static void init_smt_builtins(builtins_t *b) {
  type_t d;

  // QF_UF type
  b->utype = yices_new_uninterpreted_type();

  // QF_AX types
  b->index_type = yices_new_uninterpreted_type();
  b->elem_type = yices_new_uninterpreted_type();
  d = b->index_type;
  b->ax_array = yices_function_type(1, &d, b->elem_type);

  // Other array types
  d = yices_int_type();
  b->int_array = yices_function_type(1, &d, d);
  b->array1 = yices_function_type(1, &d, yices_real_type());
  b->array2 = yices_function_type(1, &d, b->array1);

  b->array = b->int_array;

  // Bitvector constants
  b->bit0 = yices_bvconst64_term(1, 0);
  b->bit1 = yices_bvconst64_term(1, 1);
}



/**********************
 *  BENCHMARK OBJECT  *
 *********************/

/*
 * Initialization
 */
void init_benchmark(smt_benchmark_t *bench) {
  bench->name = NULL;
  bench->logic_name = NULL;
  bench->logic_parameter = 0;
  bench->status = smt_none;
  bench->has_uf = false;
  bench->nformulas = 0;
  bench->fsize = 0;
  bench->formulas = NULL;
}

/*
 * Convert a string representing a rational constant into an positive integer
 * returns -1 if there's an error
 */
static int32_t rational_string_to_int(char *s) {
  rational_t aux;
  int result;

  q_init(&aux);
  result = q_set_from_string(&aux, s); // -1 if the format is wrong
  if (result == 0 && q_is_smallint(&aux)) {
    result = q_get_smallint(&aux);
  }
  q_clear(&aux);
  return result;
}

/*
 * Set benchmark fields from the lexer token
 */
static void set_benchmark_name(smt_benchmark_t *bench, lexer_t *lex) {
  bench->name = clone_string(tkval(lex));
  string_incref(bench->name);
}

static void set_logic_name(smt_benchmark_t *bench, lexer_t *lex) {
  bench->logic_name = clone_string(tkval(lex));
  string_incref(bench->logic_name);
}

static void set_logic_parameter(smt_benchmark_t *bench, lexer_t *lex) {
  bench->logic_parameter = rational_string_to_int(tkval(lex));
}

static void set_benchmark_status(smt_benchmark_t *bench, lexer_t *lex) {
  switch (current_token(lex)) {
  case SMT_TK_UNSAT:
    bench->status = smt_unsat;
    break;
  case SMT_TK_SAT:
    bench->status = smt_sat;
    break;
  case SMT_TK_UNKNOWN:
    bench->status = smt_unknown;
    break;
  default:
    break;
  }
}


/*
 * Add an assertion (:formula or :assumption)
 */
static void add_assertion(smt_benchmark_t *bench, term_t t) {
  uint32_t i, n;

  i = bench->nformulas;
  n = bench->fsize;
  assert(i <= n);
  if (i == n) {
    if (n < MIN_FSIZE) {
      n = MIN_FSIZE;
    } else {
      n ++;
      n += n>>1;
      if (n > MAX_FSIZE) {
        out_of_memory();
      }
    }
    bench->formulas = (term_t *) safe_realloc(bench->formulas, n * sizeof(term_t));
    bench->fsize = n;
  }
  bench->formulas[i] = t;
  bench->nformulas = i + 1;
}


/*
 * Delete bench object
 */
void delete_benchmark(smt_benchmark_t *bench) {
  if (bench->name != NULL) {
    string_decref(bench->name);
    bench->name = NULL;
  }
  if (bench->logic_name != NULL) {
    string_decref(bench->logic_name);
    bench->logic_name = NULL;
  }
  safe_free(bench->formulas);
  bench->formulas = NULL;
}



/**************
 *  PARSING   *
 *************/

/*
 * Marker for bottom of the state stack.
 */
enum {
  done = NSTATES,
};


/*
 * Read action from the tables in smt_parse_tables.h
 */
static action_t get_action(state_t s, smt_token_t tk) {
  int32_t i;

  i = ((int32_t) base[s]) + ((int32_t) tk);
  if (check[i] == s) {
    return value[i];
  } else {
    return default_value[s];
  }
}


/*
 * Main parsing procedure
 * - start = initial state
 * return -1 if there's an error, 0 otherwise
 */
static int32_t smt_parse(parser_t *parser, smt_benchmark_t *bench, state_t start) {
  smt_token_t token;
  parser_state_t state;
  parser_stack_t *stack;
  lexer_t *lex;
  tstack_t *tstack;
  int exception;
  loc_t loc;

  // auxiliary variables for SMT-LIB
  uint32_t default_bvsize;
  builtins_t builtins;
  loc_t saved_loc;
  string_buffer_t saved_symbol;

  stack = &parser->pstack;
  lex = parser->lex;
  tstack = parser->tstack;

  assert(parser_stack_is_empty(stack));
  assert(tstack_is_empty(tstack));

  // initialize all built-in types and terms, and auxiliary variables
  init_smt_builtins(&builtins);
  default_bvsize = 32;
  init_string_buffer(&saved_symbol, 60);

  // prepare to catch exceptions in term stack operations
  exception = setjmp(tstack->env);
  if (exception == 0) {

    parser_push_state(stack, done);
    state = start;

  loop:
    token = next_smt_token(lex);
    loc.line = current_token_line(lex);
    loc.column = current_token_column(lex);

    // jump here for actions that don't consume the token
  skip_token:

    switch (get_action(state, token)) {
    case next_goto_an1:
      state = an1;
      goto loop;

    case return_notoken:
      state = parser_pop_state(stack);
      goto skip_token;

    case next_goto_an0:
      state = an1;
      goto loop;

    case var_next_return:
      // term variable: must be bound to a term
      tstack_push_term_by_name(tstack, tkval(lex), &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto loop;

    case fvar_next_return:
      // formula variable: must be bound to a term
      tstack_push_term_by_name(tstack, tkval(lex), &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto loop;

    case rational_next_return:
      tstack_push_rational(tstack, tkval(lex), &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto loop;

    case float_next_return:
      tstack_push_float(tstack, tkval(lex), &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto loop;

    case bvbin_next_return:
      // skip prefix 'bvbin'
      assert(tklen(lex) > 5);
      tstack_push_bvbin(tstack, tkval(lex) + 5, tklen(lex) - 5, &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto loop;

    case bvhex_next_return:
      // skip prefix 'bvhex'
      assert(tklen(lex) > 5);
      tstack_push_bvhex(tstack, tkval(lex) + 5, tklen(lex) - 5, &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto loop;

    case true_next_return:
      tstack_push_true(tstack, &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto loop;

    case false_next_return:
      tstack_push_false(tstack, &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto loop;

    case bit0_next_return:
      tstack_push_term(tstack, builtins.bit0, &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto loop;

    case bit1_next_return:
      tstack_push_term(tstack, builtins.bit1, &loc);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto loop;

    case next_goto_bt1:
      // token is bv<digits>
      assert(token == SMT_TK_BV_CONSTANT);
      assert(tklen(lex) > 2);
      tstack_push_op(tstack, MK_BV_CONST, &loc);
      tstack_push_rational(tstack, tkval(lex) + 2, &loc);
      state = bt1;
      goto loop;

    case next_goto_bt2:
      state = bt2;
      goto loop;

    case endbvconst_return:
      // old-fashioned SMTLIB: no size given
      tstack_push_int32(tstack, default_bvsize, &loc);
      tstack_eval(tstack); // eval the MK_BV_CONST operation
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto skip_token;

    case next_goto_bt3:
      // token is a rational
      assert(token == SMT_TK_RATIONAL);
      tstack_push_rational(tstack, tkval(lex), &loc);
      state = bt3;
      goto loop;

    case next_return:
      // evaluate top command
      tstack_eval(tstack);
      assert(! parser_stack_is_empty(stack));
      state = parser_pop_state(stack);
      goto loop;

      /*
       * U is no longer a keyword: removed
       */
      //case u_next_return:
      //      tstack_push_type(tstack, builtins.utype, &loc);
      //      state = parser_pop_state(stack);
      //      goto loop;

    case int_next_return:
      tstack_push_int_type(tstack, &loc);
      state = parser_pop_state(stack);
      goto loop;

    case real_next_return:
      tstack_push_real_type(tstack, &loc);
      state = parser_pop_state(stack);
      goto loop;

    case array1_next_return:
      tstack_push_type(tstack, builtins.array1, &loc);
      state = parser_pop_state(stack);
      goto loop;

    case array2_next_return:
      tstack_push_type(tstack, builtins.array2, &loc);
      state = parser_pop_state(stack);
      goto loop;

    case sortsymbol_next_return:
      tstack_push_type_by_name(tstack, tkval(lex), &loc);
      state = parser_pop_state(stack);
      goto loop;

    case next_goto_s1:  // BitVec
      tstack_push_op(tstack, MK_BV_TYPE, &loc);
      state = s1;
      goto loop;

    case next_goto_s4:  // Array
      state = s4;
      goto loop;

    case next_goto_s2:  // [
      state = s2;
      goto loop;

    case next_goto_s3:  // size of bitvector
      tstack_push_rational(tstack, tkval(lex), &loc);
      state = s3;
      goto loop;

    case next_goto_s5:  // [
      state = s5;
      goto loop;

    case array_return:
      // old-style array: [int -> int]
      tstack_push_type(tstack, builtins.array, &loc);
      state = parser_pop_state(stack);
      goto skip_token;

    case next_goto_s6: // array[n:m] = (-> (bitvector n) (bitvector m))
      tstack_push_op(tstack, MK_FUN_TYPE, &loc);
      tstack_push_op(tstack, MK_BV_TYPE, &loc);
      tstack_push_rational(tstack, tkval(lex), &loc); // n
      tstack_eval(tstack);
      state = s6;
      goto loop;

    case next_goto_s7:
      state = s7;
      goto loop;

    case next_goto_s8:  // rest of array[n:m] (i.e., m)
      tstack_push_op(tstack, MK_BV_TYPE, &loc);
      tstack_push_rational(tstack, tkval(lex), &loc); // m
      tstack_eval(tstack);
      state = s8;
      goto loop;

    case bvarray_next_return: // build the array type
      tstack_eval(tstack);
      state = parser_pop_state(stack);
      goto loop;

    case termsymbol_next_return:
      tstack_push_term_by_name(tstack, tkval(lex), &loc);
      state = parser_pop_state(stack);
      goto loop;

    case next_goto_f1:
      state = f1;
      goto loop;

    case goto_bt0:
      state = bt0;
      goto skip_token;

    case distinct_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_DISTINCT, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case eq_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_EQ, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case not_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_NOT, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case implies_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_IMPLIES, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case if_then_else_next_push_f3_goto_f0:
    case ite_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_ITE, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case and_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_AND, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case or_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_OR, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case xor_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_XOR, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case iff_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_IFF, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case add_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_ADD, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case sub_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_SUB, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case mul_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_MUL, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case div_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_DIVISION, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case tilde_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_NEG, &loc); // unary minus
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case lt_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_LT, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case le_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_LE, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case gt_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_GT, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case ge_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_GE, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case select_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_APPLY, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case store_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_UPDATE, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvadd_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_ADD, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvsub_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SUB, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvmul_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_MUL, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvneg_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_NEG, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvor_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_OR, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvand_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_AND, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvxor_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_XOR, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvnot_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_NOT, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvlt_next_push_f3_goto_f0:
    case bvult_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_LT, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvleq_next_push_f3_goto_f0:
    case bvule_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_LE, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvgt_next_push_f3_goto_f0:
    case bvugt_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_GT, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvgeq_next_push_f3_goto_f0:
    case bvuge_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_GE, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvslt_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SLT, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvsleq_next_push_f3_goto_f0:
    case bvsle_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SLE, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvsgt_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SGT, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvsgeq_next_push_f3_goto_f0:
    case bvsge_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SGE, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case concat_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_CONCAT, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case shift_left0_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SHIFT_LEFT0, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case shift_right0_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SHIFT_RIGHT0, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case shift_left1_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SHIFT_LEFT1, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case shift_right1_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SHIFT_RIGHT1, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvudiv_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_DIV, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvurem_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_REM, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvsdiv_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SDIV, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvsrem_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SREM, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvsmod_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SMOD, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvshl_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_SHL, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvlshr_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_LSHR, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvashr_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_ASHR, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvnand_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_NAND, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvnor_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_NOR, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvxnor_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_XNOR, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvredor_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_REDOR, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvredand_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_REDAND, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case bvcomp_next_push_f3_goto_f0:
      tstack_push_op(tstack, MK_BV_COMP, &loc);
      parser_push_state(stack, f3);
      state = f0;
      goto loop;

    case symbol_next_goto_f4:
      /*
       * make a copy of the symbol. We don't know yet whether it's a
       * function application or an annotated symbol. This gets
       * determined by the next token, which leads either to
       * next_push_f27_goto_an1 or applyfun_push_f3_goto_f0
       */
      string_buffer_reset(&saved_symbol);
      string_buffer_append_buffer(&saved_symbol, lex->buffer);
      string_buffer_close(&saved_symbol);
      saved_loc = loc;
      state = f4;
      goto loop;

    case extract_next_goto_f6:
      tstack_push_op(tstack, MK_BV_EXTRACT, &loc);
      state = f6;
      goto loop;

    case rotate_left_next_goto_f9:
      tstack_push_op(tstack, MK_BV_ROTATE_LEFT, &loc);
      state = f9;
      goto loop;

    case rotate_right_next_goto_f9:
      tstack_push_op(tstack, MK_BV_ROTATE_RIGHT, &loc);
      state = f9;
      goto loop;

    case repeat_next_goto_f9:
      tstack_push_op(tstack, MK_BV_REPEAT, &loc);
      state = f9;
      goto loop;

    case zero_extend_next_goto_f9:
      tstack_push_op(tstack, MK_BV_ZERO_EXTEND, &loc);
      state = f9;
      goto loop;

    case sign_extend_next_goto_f14:
      tstack_push_op(tstack, MK_BV_SIGN_EXTEND, &loc);
      state = f14;
      goto loop;

    case let_next_goto_f16:
      tstack_push_op(tstack, LET, &loc);
      state = f16;
      goto loop;

    case exists_next_goto_f20:
      tstack_push_op(tstack, MK_EXISTS, &loc);
      state = f20;
      goto loop;

    case forall_next_goto_f20:
      tstack_push_op(tstack, MK_FORALL, &loc);
      state = f20;
      goto loop;

    case push_f5_goto_bt0:
      parser_push_state(stack, f5);
      state = bt0;
      goto skip_token;

    case next_push_f26_goto_an1:
      parser_push_state(stack, f26);
      state = an1;
      goto loop;

    case push_f3_goto_f0:
      parser_push_state(stack, f3);
      state = f0;
      goto skip_token;

    case next_push_f27_goto_an1:
      // annotated symbol
      tstack_push_term_by_name(tstack, saved_symbol.data, &saved_loc);
      parser_push_state(stack, f27);
      state = an1;
      goto loop;

    case applyfun_push_f3_goto_f0:
      // function application with saved symbol as uninterpreted function
      tstack_push_op(tstack, MK_APPLY, &saved_loc);
      tstack_push_term_by_name(tstack, saved_symbol.data, &saved_loc);
      parser_push_state(stack, f3);
      state = f0;
      goto skip_token;

    case next_return_noapply: // f27
      state = parser_pop_state(stack);
      goto loop;

    case next_goto_f7:
      state = f7;
      goto loop;

    case rational_next_goto_f8:
      tstack_push_rational(tstack, tkval(lex), &loc);
      state = f8;
      goto loop;

    case next_goto_f10:
      state = f10;
      goto loop;

    case rational_next_goto_f11:
      tstack_push_rational(tstack, tkval(lex), &loc);
      state = f11;
      goto loop;

    case next_push_f26_push_an0_goto_f0:
      parser_push_state(stack, f26);
      parser_push_state(stack, an0);
      state = f0;
      goto loop;

    case push_f15_goto_f0:
      parser_push_state(stack, f15);
      state = f0;
      goto skip_token;

    case rational_next_push_f26_goto_an0:
      // old-style sign-extend: (sign-extend <bv> <rational>)
      tstack_push_rational(tstack, tkval(lex), &loc);
      parser_push_state(stack, f26);
      state = an0;
      goto loop;

    case next_goto_f17: // open par in let/flet
      state = f17;
      goto loop;

    case var_next_push_f19_goto_f0: // var in let or flet
      tstack_push_op(tstack, BIND, &loc);
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc); // var name
      parser_push_state(stack, f19);
      state = f0;
      goto loop;

    case bind_next_push_f26_push_an0_goto_f0:
      // evaluate bind
      tstack_eval(tstack);
      parser_push_state(stack, f26);
      parser_push_state(stack, an0);
      state = f0;
      goto loop;

    case next_goto_f21: // open par in forall/exists
      state = f21;
      goto loop;

    case var_next_push_f23_goto_s0: // var in quantifier
      tstack_push_op(tstack, DECLARE_VAR, &loc);
      tstack_push_symbol(tstack, tkval(lex), tklen(lex), &loc); // var name
      parser_push_state(stack, f23);
      state = s0;
      goto loop;

    case next_goto_f24:
      // eval previous DECLARE_VAR
      tstack_eval(tstack);
      state = f24;
      goto loop;

    case next_goto_f25:
      state = f25;
      goto loop;

    case symbol_next_push_f26_goto_an0:
      // body of quantified formula is a symbol
      tstack_push_term_by_name(tstack, tkval(lex), &loc);
      parser_push_state(stack, f26);
      state = an0;
      goto loop;

    case push_f26_push_an0_goto_bt0:
      // body of quantified formula is a base term
      parser_push_state(stack, f26);
      parser_push_state(stack, an0);
      state = bt0;
      goto skip_token;

    case push_f26_push_an0_goto_f1:
      // body starts with (
      parser_push_state(stack, f26);
      parser_push_state(stack, an0);
      state = f1;
      goto skip_token;

      // benchmark
    case next_goto_b1:
      state = b1;
      goto loop;

    case next_goto_b2:
      state = b2;
      goto loop;

    case benchmarkname_next_goto_b3:
      set_benchmark_name(bench, lex);
      state = b3;
      goto loop;

    case notes_next_goto_b4:
      state = b4;
      goto loop;

    case status_next_goto_b5:
      state = b5;
      goto loop;

    case assert_next_push_b6_goto_f0:
      tstack_push_op(tstack, BUILD_TERM, &loc); // or ASSERT_CMD?
      parser_push_state(stack, b6);
      state = f0;
      goto loop;

    case eval_assert_goto_b3:
      tstack_eval(tstack);
      add_assertion(bench, tstack_get_term(tstack));
      state = b3;
      goto skip_token;

    case logic_next_goto_b7:
      state = b7;
      goto loop;

    case extrasorts_next_goto_b11:
      state = b11;
      goto loop;

    case extrapreds_next_goto_b14:
      state = b14;
      goto loop;

    case extrafuns_next_goto_b20:
      state = b20;
      goto loop;

    case next_push_b3_goto_an1:
      parser_push_state(stack, b3);
      state = an1;
      goto loop;

    case end_benchmark_return:
      state = parser_pop_state(stack);
      assert(state == done);
      goto the_end;

    case next_goto_b3:
      state = b3;
      goto loop;

    case sat_next_goto_b3:
    case unsat_next_goto_b3:
    case unknown_next_goto_b3:
      set_benchmark_status(bench, lex);
      state = b3;
      goto loop;


    case logicname_next_goto_b8:
      set_logic_name(bench, lex);
      smt_lexer_activate_logic(smt_logic_code(bench->logic_name));
      if (strcmp(bench->logic_name, "QF_UF") == 0) {
        // declare the predefined type "U"
        yices_set_type_name(builtins.utype, "U");
      } else if (strcmp(bench->logic_name, "QF_AX") == 0) {
        /*
         * remap the predefined type "Array" to ax_array
         * declare the types Index and Element
         */
        builtins.array = builtins.ax_array;
        yices_set_type_name(builtins.index_type, "Index");
        yices_set_type_name(builtins.elem_type, "Element");
      }
      state = b8;
      goto loop;

    case next_goto_b9: // '['  in QF_UFBV[<size>]
      state = b9;
      goto loop;

    case goto_b3:
      state = b3;
      goto skip_token;

    case rational_next_goto_b10:
      set_logic_parameter(bench, lex);
      state = b10;
      goto loop;

    case endlogic_next_goto_b3:
      // check logic name and parameter here.
      // save integer parameter of logic
      if (strcmp(bench->logic_name, "QF_UFBV") == 0) {
        default_bvsize = bench->logic_parameter;
        if (default_bvsize <= 0) {
          fprintf(stderr, "invalid bitsize in :theory QF_UFBV\n");
          goto cleanup;
        }
      }
      state = b3;
      goto loop;

    case next_goto_b12:
      state = b12;
      goto loop;

    case sortsymbol_next_goto_b13:
      // declare uninterpreted type
      tstack_push_op(tstack, DEFINE_TYPE, &loc);
      tstack_push_free_typename(tstack, tkval(lex), tklen(lex), &loc);
      tstack_eval(tstack);
      state = b13;
      goto loop;

    case next_goto_b15:
      state = b15;
      goto loop;

    case next_goto_b16:
      state = b16;
      goto loop;

    case predsymbol_next_goto_b17:
      // new predicate name
      tstack_push_op(tstack, DEFINE_TERM, &loc);
      tstack_push_free_termname(tstack, tkval(lex), tklen(lex), &loc);
      tstack_push_op(tstack, MK_FUN_TYPE, &loc);
      // mk_fun_type with no domain and range boolean does the right thing
      state = b17;
      goto loop;

    case next_goto_b19:
      // declare predicate
      tstack_push_bool_type(tstack, &loc);
      tstack_eval(tstack); // construct the type
      tstack_eval(tstack); // evaluate DEFINE_TERM
      state = b19;
      goto loop;

    case next_push_b18_goto_an1:
      parser_push_state(stack, b18);
      state = an1;
      goto loop;

    case push_b17_goto_s0:
      /*
       * This is taken in :extrapreds ((P T1 ... Tn))
       * but not in :extrapreds ((P))
       * so it indicates predicates with arity > 0.
       */
      bench->has_uf = true;
      parser_push_state(stack, b17);
      state = s0;
      goto skip_token;

    case next_goto_b21:
      state = b21;
      goto loop;

    case next_goto_b22:
      state = b22;
      goto loop;

    case funsymbol_next_push_b24_goto_s0:
      // new predicate name
      tstack_push_op(tstack, DEFINE_TERM, &loc);
      tstack_push_free_termname(tstack, tkval(lex), tklen(lex), &loc);
      tstack_push_op(tstack, MK_FUN_TYPE, &loc);
      // mk_fun_type with no domain does the right thing
      parser_push_state(stack, b24);
      state = s0;
      goto loop;

    case next_goto_b25:
      // declare function or constant
      tstack_eval(tstack); // construct the type
      tstack_eval(tstack); // evaluate DEFINE_TERM
      state = b25;
      goto loop;

    case next_push_b27_goto_an1:
      parser_push_state(stack, b27);
      state = an1;
      goto loop;

    case push_b24_goto_s0:
      /*
       * This transition is taken in
       *   :extrafuns ((name T1 T2 ... Tn))
       * but not in
       *   :extrafuns  ((name T1))
       * so it indicates functions with arity > 0.
       */
      bench->has_uf = true;
      parser_push_state(stack, b24);
      state = s0;
      goto skip_token;

    case error_rational_expected:
      syntax_error(lex, SMT_TK_RATIONAL);
      goto cleanup;

    case error_rb_expected:
      syntax_error(lex, SMT_TK_RB);
      goto cleanup;

    case error_lb_expected:
      syntax_error(lex, SMT_TK_LB);
      goto cleanup;

    case error_colon_expected:
      syntax_error(lex, SMT_TK_COLON);
      goto cleanup;

    case error_attribute_expected:
      syntax_error(lex, SMT_TK_ATTRIBUTE);
      goto cleanup;

    case error_lp_expected:
      syntax_error(lex, SMT_TK_LP);
      goto cleanup;

    case error_rp_expected:
      syntax_error(lex, SMT_TK_RP);
      goto cleanup;

    case error_var_expected:
      syntax_error(lex, SMT_TK_VAR);
      goto cleanup;

    case error_benchmark_expected:
      syntax_error(lex, SMT_TK_BENCHMARK);
      goto cleanup;

    case error_symbol_expected:
      syntax_error(lex, SMT_TK_SYMBOL);
      goto cleanup;

    case error_string_expected:
      syntax_error(lex, SMT_TK_STRING);
      goto cleanup;

    case error_status_expected:
      syntax_error(lex, SMT_TK_STATUS);
      goto cleanup;

    case error:
      syntax_error(lex, -1);
      goto cleanup;

    }

  } else {
    term_stack_smt_error(stderr, reader_name(lex), tstack, exception);
    goto cleanup;
  }

 cleanup:
  tstack_reset(tstack);
  parser_stack_reset(stack);
  delete_string_buffer(&saved_symbol);
  return -1;

 the_end:
  delete_string_buffer(&saved_symbol);
  return 0;
}


/*
 * Top-level call
 */
int32_t parse_smt_benchmark(parser_t *parser, smt_benchmark_t *bench) {
  return smt_parse(parser, bench, b0);
}


