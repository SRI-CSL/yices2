/*
 * Parser for the Yices language.
 */

#include <stdio.h>
#include <setjmp.h>
#include <inttypes.h>

#include "yices_parse_tables.h"
#include "yices_parser.h"
#include "yices_lexer.h"


/*
 * Error messages
 */
static const char * const code2string[NUM_TSTACK_ERRORS] = {
  "no error",
  "internal error",
  "operation not supported",
  "undefined term",
  "undefined type",
  "invalid rational format",
  "invalid float format",
  "invalid bitvector binary format",
  "invalid bitvector hexadecimal format",
  "cannot redefine type",
  "cannot redefine term",
  "duplicate name in scalar type",
  "duplicate variable name",
  "invalid operation",
  "wrong number of arguments",
  "constant too large",
  "constant is not an integer",
  "symbol required",
  "numerical constant required",
  "type required",
  "error in arithmetic operation",
  "division by zero",
  "divisor is not a constant",
  "bitsize must be positive",
  "number cannot be converted to a bitvector",
  "error in bitvector arithmetic operation",
  "error in bitvector operation",
  "incompatible types in define",
  "yices error",
};


/*
 * Translate opcode to string (for diagnosis)
 */
static const char * const opcode2string[NUM_OPCODES] = {
  "no_op",
  "define-type",
  "define",
  "bind",
  "declare_var",
  "let",

  "bitvector type",
  "scalar type",
  "tuple type",
  "function type",

  "function application",
  "if-then-else",
  "equality",
  "disequality",
  "distinct",
  "not",
  "or",
  "and",
  "xor",
  "<=>",
  "=>",
  "mk-tuple",
  "select",
  "update",
  "forall",
  "exists",

  "addition",
  "subtraction",
  "negation",
  "multiplication",
  "division",
  "inequality",
  "inequality",
  "inequality",
  "inequality",

  "mk-bv",
  "bv-add",
  "bv-sub",
  "bv-mul",
  "bv-neg",
  "bv-not",
  "bv-and",
  "bv-or",
  "bv-xor",
  "bv-nand",
  "bv-nor",
  "bv-xnor",
  "bv-shift-left0",
  "bv-shift-left1",
  "bv-shift-right0",
  "bv-shift-right1",
  "bv-ashift-right",
  "bv-rotate-left",
  "bv-rotate-right",
  "bv-extract",
  "bv-concat",
  "bv-repeat",
  "bv-sign-extend",
  "bv-zero-extend",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",

  "bv-shl",
  "bv-lshr",
  "bv-ashr",
  "bv-udiv",
  "bv-urem",
  "bv-sdiv",
  "bv-srem",
  "bv-smod",
  "bv-redor",
  "bv-redand",
  "bv-comp",

  "build term",
  "build type",

  "exit",
  "check",
  "echo",
  "include",
  "assert",
  "push",
  "pop",
  "reset",
  "show-model",
  "eval",
  "dump-context",
};



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
 * Print a message on a syntax error
 * - lex = the lexer
 * - expected_token = what was expected or -1
 */
static void syntax_error(lexer_t *lex, token_t expected_token) {
  yices_token_t tk;
  reader_t *rd;

  tk = current_token(lex);
  rd = &lex->reader;

  if (rd->name != NULL) {
    fprintf(stderr, "%s: ", rd->name);
  }

  switch (tk) {
  case TK_OPEN_STRING:
    fprintf(stderr, "missing string terminator \" (line %"PRId32", column %"PRId32")\n", 
	    rd->line, rd->column);
    return;
  case TK_EMPTY_BVCONST:
    fprintf(stderr, "invalid binary constant %s (line %"PRId32", column %"PRId32")\n", 
	    tkval(lex), lex->tk_line, lex->tk_column);
    return;
  case TK_EMPTY_HEXCONST:
    fprintf(stderr, "invalid hexadecimal constant %s (line %"PRId32", column %"PRId32")\n", 
	    tkval(lex), lex->tk_line, lex->tk_column);
    return;
  case TK_INVALID_NUM:
    fprintf(stderr, "invalid number %s (line %"PRId32", column %"PRId32")\n", 
	    tkval(lex), lex->tk_line, lex->tk_column);
    return;
  case TK_ZERO_DIVISOR:
    fprintf(stderr, "zero divisor in constant %s (line %"PRId32", column %"PRId32")\n", 
	    tkval(lex), lex->tk_line, lex->tk_column);
    return;
  case TK_ERROR:
    fprintf(stderr, "invalid token %s (line %"PRId32", column %"PRId32")\n", 
	    tkval(lex), lex->tk_line, lex->tk_column);
    return;

  default:
    if (expected_token != -1) {
      fprintf(stderr, "syntax error (line %"PRId32", column %"PRId32"): %s expected\n",
	      lex->tk_line, lex->tk_column, yices_token_to_string(expected_token));
    } else {
      fprintf(stderr, "syntax error (line %"PRId32", column %"PRId32")\n", 
	      lex->tk_line, lex->tk_column);
    }
  } 
}


/*
 * Error reported by term_api:
 * - tstack->error_op = operation being executed
 * - tstack->error_loc = location of the argument expression (approximate)
 *   that triggered the error
 */
static void yices_error(lexer_t *lex, tstack_t *tstack) {
  error_report_t *error;
  reader_t *rd;


  rd = &lex->reader;
  if (rd->name != NULL) {
    fprintf(stderr, "%s: ", rd->name);
  }
  fprintf(stderr, "error in %s, line %"PRId32", column %"PRId32": ",
	  opcode2string[tstack->error_op], tstack->error_loc.line, tstack->error_loc.column);
    
  error = yices_get_error_report();
  switch (error->code) {
  case NO_ERROR:
    // should not happen
    fprintf(stderr, "bad error code %"PRIu32" (this is a bug)\n", error->code);
    break;
  case INVALID_TYPE:
    // should not happen
    fprintf(stderr, "invalid type %"PRId32" (this is a bug)\n", error->type1);
    break;
  case INVALID_TERM:
    // should not happen
    fprintf(stderr, "invalid term: %"PRId32" (this is a bug)\n", error->term1);
    break;
  case POS_INT_REQUIRED:
    fprintf(stderr, "integer argument must be positive\n");
    break;
  case NONNEG_INT_REQUIRED:
    fprintf(stderr, "integer argument must be non-negative\n");
    break;
  case TOO_MANY_ARGUMENTS:
    fprintf(stderr, "maximal arity exceeded (limit = %"PRIu32")\n", YICES_MAX_ARITY);
    break;
  case TOO_MANY_VARS:
    fprintf(stderr, "too many variables (limit = %"PRIu32")\n", YICES_MAX_VARS);
    break;
  case MAX_BVSIZE_EXCEEDED:
    fprintf(stderr, "bitvector size too large (max = %"PRIu32")\n", YICES_MAX_BVSIZE);
    break;
  case SCALAR_OR_UTYPE_REQUIRED:
    fprintf(stderr, "invalid type in constant creation\n");
    break;
  case FUNCTION_REQUIRED:
    fprintf(stderr, "argument is not a function\n");
    break;
  case TUPLE_REQUIRED:
    fprintf(stderr, "argument is not a tuple\n");
    break;
  case VARIABLE_REQUIRED:
    fprintf(stderr, "argument is not a variable\n");
    break;
  case INVALID_CONSTANT_INDEX:
    fprintf(stderr, "invalid index %"PRId32" in constant creation\n", error->badval);
    break;
  case WRONG_NUMBER_OF_ARGUMENTS:
    fprintf(stderr, "wrong number of arguments\n");
    break;
  case TYPE_MISMATCH:
    fprintf(stderr, "type mismatch: invalid argument\n");
    break;
  case INCOMPATIBLE_TYPES:
    fprintf(stderr, "incompatible types\n");
    break;
  case INVALID_TUPLE_INDEX:
    fprintf(stderr, "invalid index\n");
    break;
  case DUPLICATE_VARIABLE:
    fprintf(stderr, "duplicate variable in quantifier\n");
    break;
  case ARITHTERM_REQUIRED:
    fprintf(stderr, "arithmetic argument required\n");
    break;
  case DEGREE_OVERFLOW:
    fprintf(stderr, "degree is too large\n");
    break;
  case BITVECTOR_REQUIRED:
    fprintf(stderr, "bitvector argument required\n");
    break;
  case INCOMPATIBLE_BVSIZES:
    fprintf(stderr, "incompatible bitsizes\n");
    break;    
  case INVALID_BITSHIFT:
    fprintf(stderr, "invalid index in shift or rotate\n");
    break;
  case INVALID_BVEXTRACT:
    fprintf(stderr, "invalid index in bv-extract\n");
    break;
  case INVALID_BVSIGNEXTEND:
    fprintf(stderr, "invalid index in sign-extend\n");
    break;
  case INVALID_BVZEROEXTEND:
    fprintf(stderr, "invalid index in zero-extend\n");
    break;    
  case EMPTY_BITVECTOR:
    fprintf(stderr, "bitvectors must have positive bitsize\n");
    break;
  }
}


/*
 * Print a message on an exception from tstack
 */
static void tstack_error(lexer_t *lex, tstack_t *tstack, tstack_error_t exception) {
  reader_t *rd;
  
  assert(exception != TSTACK_NO_ERROR);

  if (exception == TSTACK_YICES_ERROR) {
    yices_error(lex, tstack);
    return;
  }

  rd = &lex->reader;
  if (rd->name != NULL) {
    fprintf(stderr, "%s: %s ", rd->name, code2string[exception]);
  } else {
    fprintf(stderr, "Error: %s ", code2string[exception]);
  }

  switch (exception) {
  case TSTACK_INTERNAL_ERROR:
  case TSTACK_INVALID_OP:
  case TSTACK_NOT_A_SYMBOL:
  case TSTACK_NOT_A_TYPE:
    fprintf(stderr, "opcode = %d (this is a bug)\n", tstack->error_op);
    break;

  case TSTACK_INVALID_FRAME:
    fprintf(stderr, "in %s (line %"PRId32", column %"PRId32")\n",
	    opcode2string[tstack->error_op], tstack->error_loc.line, tstack->error_loc.column);
    break;

  case TSTACK_OP_NOT_IMPLEMENTED:
    fprintf(stderr, "opcode = %d\n", tstack->error_op);
    break;
    

  case TSTACK_UNDEF_TERM:
  case TSTACK_UNDEF_TYPE:
  case TSTACK_DUPLICATE_SCALAR_NAME:
  case TSTACK_DUPLICATE_VAR_NAME:
  case TSTACK_RATIONAL_FORMAT:
  case TSTACK_FLOAT_FORMAT:
  case TSTACK_BVBIN_FORMAT:
  case TSTACK_BVHEX_FORMAT:
  case TSTACK_TYPENAME_REDEF:
  case TSTACK_TERMNAME_REDEF:
    fprintf(stderr, "%s (line %"PRId32", column %"PRId32")\n",
	    tstack->error_string, tstack->error_loc.line, tstack->error_loc.column);
    break;

  case TSTACK_NOT_A_RATIONAL:
  case TSTACK_INTEGER_OVERFLOW:
  case TSTACK_NOT_AN_INTEGER:
  case TSTACK_ARITH_ERROR:
  case TSTACK_DIVIDE_BY_ZERO:
  case TSTACK_NON_CONSTANT_DIVISOR:
  case TSTACK_NEGATIVE_BVSIZE:
  case TSTACK_INVALID_BVCONSTANT:
  case TSTACK_BVARITH_ERROR:
  case TSTACK_BVLOGIC_ERROR:
  case TSTACK_TYPE_ERROR_IN_DEFTERM:
    fprintf(stderr, "(line %"PRId32", column %"PRId32")\n",
	    tstack->error_loc.line, tstack->error_loc.column);
    break;

  default:
    break;
  }
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
 * return -1 if there's an error, 0 otherwise
 */
static int32_t yices_parse(parser_t *parser, state_t start) {
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
  assert(tstack_is_empty(tstack));

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

    case assert_next_push_r0_goto_e0:
      tstack_push_op(tstack, ASSERT_CMD, &loc);
      parser_push_state(stack, r0);
      state = e0;
      goto loop;
      
    case deftype_next_goto_c2:
      tstack_push_op(tstack, DEFINE_TYPE, &loc);
      state = c2;
      goto loop;

    case defterm_next_goto_c6:
      tstack_push_op(tstack, DEFINE_TERM, &loc);
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

    case showparams_next_goto_r0:
      tstack_push_op(tstack, SHOW_PARAMS_CMD, &loc);
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
      tstack_push_string(tstack, tkval(lex), tklen(lex), &loc);
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
      tstack_push_op(tstack, MK_DIV, &loc);
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
      tstack_push_string(tstack, tkval(lex), tklen(lex), &loc);
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
      tstack_push_string(tstack, tkval(lex), tklen(lex), &loc);
      state = e12;
      goto loop;

    case e14_next_push_r0_goto_e0:
      // end of var decls
      tstack_eval(tstack); // eval last binding
      parser_push_state(stack, r0);
      state = e0;
      goto loop;

    case next_goto_e16:
      state = e16;
      goto loop;

    case next_goto_e17:
      state = e17;
      goto loop;

    case termname_next_push_e19_goto_e0:
      // name in binding
      tstack_push_op(tstack, BIND, &loc);
      tstack_push_string(tstack, tkval(lex), tklen(lex), &loc);
      parser_push_state(stack, e19);
      state = e0;
      goto loop;

    case next_goto_e20:
      // end of let binding: evaluate the binding
      tstack_eval(tstack);
      state = e20;
      goto loop;

    case error_lpar_expected:
      syntax_error(lex, TK_LP);
      goto cleanup;

    case error_symbol_expected:
      syntax_error(lex, TK_SYMBOL);
      goto cleanup;

    case error_string_expected: 
      syntax_error(lex, TK_STRING);
      goto cleanup;

    case error_colon_colon_expected:
      syntax_error(lex, TK_COLON_COLON);
      goto cleanup;

   case error_rational_expected:
      syntax_error(lex, TK_NUM_RATIONAL);
      goto cleanup;

    case error_rpar_expected:
      syntax_error(lex, TK_RP);
      goto cleanup;

    case error:
      syntax_error(lex, -1);
      goto cleanup;

    }

  } else {
    // exception raised by term_stack
    tstack_error(lex, tstack, exception);
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
extern int32_t parse_yices_command(parser_t *parser) {
  return yices_parse(parser, c0);
}

extern term_t parse_yices_term(parser_t *parser) {
  loc_t loc;
  loc.line = 0;
  loc.column = 0;
  tstack_push_op(parser->tstack, BUILD_TERM, &loc);
  if (yices_parse(parser, e0) < 0) {
    return NULL_TERM;
  }
  tstack_eval(parser->tstack);
  return tstack_get_term(parser->tstack);
}


extern type_t parse_yices_type(parser_t *parser) {
  loc_t loc;
  loc.line = 0;
  loc.column = 0;
  tstack_push_op(parser->tstack, BUILD_TYPE, &loc);
  if (yices_parse(parser, t0) < 0) {
    return NULL_TYPE;
  }
  tstack_eval(parser->tstack);
  return tstack_get_type(parser->tstack);
}


