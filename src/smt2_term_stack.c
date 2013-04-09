/*
 * OPERATIONS FOR SMT-LIB 2.0
 */

#include "attribute_values.h"
#include "tstack_internals.h"
#include "smt2_term_stack.h"


/*
 * Utilities to raise exceptions
 */
static int invalid_tag(tag_t tg) {
  int error_code;

  switch (tg) {
  case TAG_SYMBOL: 
    error_code = TSTACK_NOT_A_SYMBOL;
    break;

  case TAG_STRING:
    error_code = TSTACK_NOT_A_STRING;
    break;

  case TAG_RATIONAL:
    error_code = TSTACK_NOT_A_RATIONAL;
    break;

  default:
    error_code = TSTACK_INTERNAL_ERROR;
    break;
  }

  return error_code;
}

static void check_tag(tstack_t *stack, stack_elem_t *e, tag_t tg) {
  if (e->tag != tg) raise_exception(stack, e, invalid_tag(tg));
}

static void check_op(tstack_t *stack, int32_t op) {
  if (stack->top_op != op) {
    raise_exception(stack, stack->elem + stack->frame, TSTACK_INTERNAL_ERROR);
  }
}

static void check_size(tstack_t *stack, bool cond) {
  if (! cond) {
    raise_exception(stack, stack->elem + stack->frame, TSTACK_INVALID_FRAME);
  }
}



/*
 * Convert element e to an attribute value
 * - raise exception SMT2_INVALID_VALUE if that can't be done
 */
static aval_t get_aval(tstack_t *stack, stack_elem_t *e) {
  aval_t v;

  switch (e->tag) {
  case TAG_SYMBOL:
    v = smt2_symbol_attr(e->val.symbol);
    break;

  case TAG_STRING: 
    v = smt2_string_attr(e->val.symbol);
    break;

  case TAG_BV64:
    v = smt2_bv64_attr(e->val.bv64.bitsize, e->val.bv64.value);
    break;

  case TAG_BV:
    v = smt2_bv_attr(e->val.bv.bitsize, e->val.bv.data);
    break;

  case TAG_RATIONAL:
    v = smt2_rational_attr(&e->val.rational);
    break;

  case TAG_ATTRIBUTE:
    v = e->val.aval;
    break;

  default:
    raise_exception(stack, e, TSTACK_INTERNAL_ERROR);
    break;
  }

  return v;
}


/*
 * Store an attribute value on top of the stack (replace the current top_op)
 */
static void set_aval_result(tstack_t *stack, aval_t v) {
  stack_elem_t *e;

  e = stack->elem + (stack->top - 1);
  e->tag = TAG_ATTRIBUTE:
  e->val.aval = v;
}

/*
 * NEW OPCODES
 */

/*
 * [exit]
 */
static void check_smt2_exit(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_EXIT);
  check_size(stack, n == 0);
} 

static void eval_smt2_exit(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_exit();
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [get-assertions]
 */
static void check_smt2_get_assertions(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_GET_ASSERTIONS);
  check_size(stack, n == 0);
}

static void eval_smt2_get_assertions(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_get_assertions();
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [get-assignment]
 */
static void check_smt2_get_assignment(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_GET_ASSIGNMENT);
  check_size(stack, n == 0);
}

static void eval_smt2_get_assignment(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_get_assignment();
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [get-proof]
 */
static void check_smt2_get_proof(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_GET_PROOF);
  check_size(stack, n == 0);
}

static void eval_smt2_get_proof(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_get_proof();
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [get-unsat_core]
 */
static void check_smt2_get_unsat_core(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_GET_UNSAT_CORE);
  check_size(stack, n == 0);
}

static void eval_smt2_get_unsat_core(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_get_unsat_core();
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [get-value <term> .... <term>]
 */
static void check_smt2_get_value(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_GET_VALUE);
  check_size(stack, n >= 1);
}

static void eval_smt2_get_value(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t *a;
  uint32_t i;

  a = get_aux_buffer(stack);
  for (i=0; i<n; i++) {
    a[i] = get_term(stack, f + i);
  }
  smt2_get_value(a, n);

  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [get-option <name> ]
 */
static void check_smt2_get_option(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_GET_OPTION);
  check_size(stack, n == 1);
  check_tag(stack, f, TAG_SYMBOL); // must be a keyword
}

static void eval_smt2_get_option(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_get_option(f[0].val.symbol);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [get-info <name> ]
 */
static void check_smt2_get_info(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_GET_INFO);
  check_size(stack, n == 1);
  check_tag(stack, f, TAG_SYMBOL); // must be a keyword
}

static void eval_smt2_get_info(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_get_info(f[0].val.symbol);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [set-option <name> <value> ] or [set-option]
 */
static void check_smt2_set_option(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_SET_OPTION);
  check_size(stack, n == 1 || n == 2);
  check_tag(stack, f, TAG_SYMBOL);
}

static void eval_smt2_set_option(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  aval_t v;

  v = AVAL_NULL;
  if (n == 2) {
    v = get_aval(stack, f+1);
  }
  smt2_set_option(f[0].val.symbol, v);
  pop_frame(stack);
  no_result(stack);
}


/*
 * [set-info <name> <value>] or [set-info <name>]
 */
static void check_smt2_set_info(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_SET_INFO);
  check_size(stack, n == 1 || n == 2);
  check_tag(stack, f, TAG_SYMBOL);
}

static void eval_smt2_set_info(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  aval_t v;

  v = AVAL_NULL;
  if (n == 2) {
    v = get_aval(stack, f+1);
  }
  smt2_set_option(f[0].val.symbol, v);
  pop_frame(stack);
  no_result(stack);
}


/*
 * [set-logic <name> ]
 */
static void check_smt2_set_logic(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_SET_LOGI);
  check_size(stack, n == 1);
  check_tag(stack, f, TAG_SYMBOL);
}

static void eval_smt2_set_logic(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_set_logic(f[0].val.symbol);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [push <number> ]
 */
static void check_smt2_push(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_PUSH);
  check_size(stack, n == 1);
  check_tag(stack, f, TAG_RATIONAL);
}

static void eval_smt2_push(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t i;

  i = get_integer(stack, f);
  if (i < 0) {
    // should not happen: in SMT2, numerals are non-negative (cf. smt2_lexer)
    raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
  }
  smt2_push(i);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [pop <number> ]
 */
static void check_smt2_pop(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_PUSH);
  check_size(stack, n == 1);
  check_tag(stack, f, TAG_RATIONAL);
}

static void eval_smt2_pop(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t i;

  i = get_integer(stack, f);
  if (i < 0) {
    // should not happen: in SMT2, numerals are non-negative (cf. smt2_lexer)
    raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
  }
  smt2_pop(i);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [assert <term> ]
 */
static void check_smt2_assert(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_ASSERT);
  check_size(stack, n == 1);
}


static void eval_smt2_assert(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t t;

  t = get_term(stack, f);
  smt2_assert(t);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [check-sat ]
 */
static void check_smt2_check_sat(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_CHECK_SAT);
  check_size(stack, n == 0);
}

static void eval_smt2_check_sat(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_check_sat();
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [declare-sort <symbol> <numeral>]
 */
static void check_smt2_declare_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_DECLARE_SORT);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_SYMBOL);
  check_tag(stack, f+1, TAG_RATIONAL);
}

static void eval_smt2_declare_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t i;

  i = get_integer(stack, f+1);
  if (i < 0) {
    // should not happen: in SMT2, numerals are non-negative (cf. smt2_lexer)
    raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
  }
  smt2_declare_sort(f[0].val.symbol, i);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [define-sort <symbol> <type-binding> ... <type-binding> <type>]
 */
static void check_smt2_define_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_define_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [declare-fun <symbol> <sort> ... <sort>]
 */
static void check_smt2_declare_fun(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_declare_fun(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [define-fun <symbol> <binding> ... <binding> <sort> <term> ]
 */
static void check_smt2_define_fun(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_define_fun(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * ATTRIBUTES
 */


/*
 * [make-attr-list <value> ... <value> ]
 */
static void check_smt2_make_attr_list(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_make_attr_list(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [add-attributes <term> <keyword> <value> ... ]
 * - only attributes kept are :named and :pattern 
 */
static void check_smt2_add_attributes(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_add_attributes(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * SORT/TERM CONSTRUCTORS
 */

/*
 * [indexed-sort <symbol> <numeral> ... <numeral> ]
 */
static void check_smt2_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [app-indexed-sort <symbol> <numeral> ... <numeral> <type> ... <type>]
 */
static void check_smt2_app_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_app_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [indexed-term <symbol> <numeral> ... <numeral> ]
 */
static void check_smt2_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [sorted-term <symbol> <type>]
 */
static void check_smt2_sorted_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_sorted_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [sorted-index-term <symbol> <numeral> ... <numeral> <type>]
 */
static void check_smt2_sorted_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_sorted_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [indexed-apply <symbol> <numeral> ... <numeral> ]
 */
static void check_smt2_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [sorted-apply <symbol> <type>]
 */
static void check_smt2_sorted_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_sorted_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [sorted-index-apply <symbol> <numeral> ... <numeral> <type>]
 */
static void check_smt2_sorted_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_sorted_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


