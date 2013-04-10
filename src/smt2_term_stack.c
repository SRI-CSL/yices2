/*
 * OPERATIONS FOR SMT-LIB 2.0
 */

#include <string.h>

#include "attribute_values.h"
#include "tstack_internals.h"
#include "smt2_lexer.h"
#include "smt2_term_stack.h"
#include "smt2_commands.h"


/*
 * Convert element e to an attribute value
 * - raise exception INTERNAL_ERROR if that can't be done
 */
static aval_t get_aval(tstack_t *stack, stack_elem_t *e) {
  aval_t v;

  assert(stack->avtbl != NULL);

  switch (e->tag) {
  case TAG_SYMBOL:
    v = attr_vtbl_symbol(stack->avtbl, e->val.symbol);
    break;

  case TAG_STRING: 
    v = attr_vtbl_string(stack->avtbl, e->val.symbol);
    break;

  case TAG_BV64:
    v = attr_vtbl_bv64(stack->avtbl, e->val.bv64.bitsize, e->val.bv64.value);
    break;

  case TAG_BV:
    v = attr_vtbl_bv(stack->avtbl, e->val.bv.bitsize, e->val.bv.data);
    break;

  case TAG_RATIONAL:
    v = attr_vtbl_rational(stack->avtbl, &e->val.rational);
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
 * Convert element e into an smt2_keyword 
 * - raise exception INTERNAL_ERROR if e is not a symbol
 */
static smt2_keyword_t get_keyword(tstack_t *stack, stack_elem_t *e) {
  uint32_t len;

  if (e->tag != TAG_SYMBOL) {
    raise_exception(stack, e, TSTACK_INTERNAL_ERROR);
  }

  len = strlen(e->val.symbol);
  return smt2_string_to_keyword(e->val.symbol, len);
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

  a = get_aux_buffer(stack, n);
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
  tstack_pop_frame(stack);
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
  smt2_set_info(f[0].val.symbol, v);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [set-logic <name> ]
 */
static void check_smt2_set_logic(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_SET_LOGIC);
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
  check_op(stack, SMT2_DEFINE_SORT);
  check_size(stack, n >= 2);
  check_tag(stack, f, TAG_SYMBOL);
  check_all_tags(stack, f+1, f+(n-1), TAG_TYPE_BINDING);
  check_distinct_type_binding_names(stack, f+1, n-2);
  check_tag(stack, f+(n-1), TAG_TYPE);
}

static void eval_smt2_define_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  type_t *a;
  uint32_t i, nvars;

  nvars = n - 2;
  a = get_aux_buffer(stack, nvars);
  for (i=0; i<nvars; i++) {
    a[i] = f[i+1].val.type_binding.type;
  }

  smt2_define_sort(f[0].val.symbol, nvars, a, f[n-1].val.type);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [declare-fun <symbol> <sort> ... <sort>]
 */
static void check_smt2_declare_fun(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_DECLARE_FUN);
  check_size(stack, n>=2);
  check_tag(stack, f, TAG_SYMBOL);
  check_all_tags(stack, f+1, f+n, TAG_TYPE);
}

static void eval_smt2_declare_fun(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  type_t *a;
  uint32_t i, ntypes;

  ntypes = n - 1;
  a = get_aux_buffer(stack, ntypes);
  for (i=0; i<n; i++) {
    a[i] = f[i+1].val.type;
  }

  smt2_declare_fun(f[0].val.symbol, ntypes, a);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [define-fun <symbol> <binding> ... <binding> <sort> <term> ]
 */
static void check_smt2_define_fun(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_DEFINE_FUN);
  check_size(stack, n >= 3);
  check_tag(stack, f, TAG_SYMBOL);
  check_all_tags(stack, f+1, f+(n-2), TAG_BINDING);
  check_distinct_binding_names(stack, f+1, n-3);
  check_tag(stack, f+(n-2), TAG_TYPE);
}

static void eval_smt2_define_fun(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t *a;
  term_t body;
  uint32_t i, nvars;

  body = get_term(stack, f+(n-1));

  nvars = n-3;
  a = get_aux_buffer(stack, nvars);
  for (i=0; i<nvars; i++) {
    a[i] = f[i+1].val.binding.term;
  }

  smt2_define_fun(f[0].val.symbol, nvars, a, body, f[n-2].val.type);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * ATTRIBUTES
 */

/*
 * [make-attr-list <value> ... <value> ]
 */
static void check_smt2_make_attr_list(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_MAKE_ATTR_LIST);
}

static void eval_smt2_make_attr_list(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  aval_t *a;
  uint32_t i;
  aval_t v;

  a = get_aux_buffer(stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_aval(stack, f + i);
  }
  v = attr_vtbl_list(stack->avtbl, n, a);

  tstack_pop_frame(stack);
  set_aval_result(stack, v);
}



/*
 * [add-attributes <term> <keyword> <value> ... ]
 * - only attributes kept are :named and :pattern 
 */
static void check_smt2_add_attributes(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_ADD_ATTRIBUTES);  
  check_size(stack, n>=1);
}

// check whether f[i] is in the frame (i.e., i<n) and has tag == SYMBOL
static void check_name(tstack_t *stack, stack_elem_t *f, uint32_t i, uint32_t n) {
  if (i == n || f[i].tag != TAG_SYMBOL) {
    raise_exception(stack, f, SMT2_MISSING_NAME);
  }
}

// check whether f[i] is in the frame and is a term
// return the term if so, raise an exception otherwise
static term_t check_pattern(tstack_t *stack, stack_elem_t *f, uint32_t i, uint32_t n) {
  if (i == n) raise_exception(stack, f, SMT2_MISSING_PATTERN);
  return get_term(stack, f+i);
}

static void eval_smt2_add_attributes(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t t, pattern;
  uint32_t i;

  t = get_term(stack, f);

  i = 1;
  while (i<n) {
    switch (get_keyword(stack, f+i)) {
    case SMT2_KW_NAMED:
      i ++;
      check_name(stack, f, i, n);
      smt2_add_name(t, f[i].val.symbol);
      break;

    case SMT2_KW_PATTERN:
      i ++;
      pattern = check_pattern(stack, f, i, n);
      smt2_add_pattern(t, pattern);
      break;

    default:
      // ignore the attribute and skip the attribute value if there's one
      i ++;
      if (i < n && f[i].tag != TAG_SYMBOL) {
	i ++; 
      }
      break;
    }
  }

  tstack_pop_frame(stack);
  no_result(stack);
}



/*
 * PROCESS SYMBOLS
 */

/*
 * All functions below are variants of push_symbol
 * - s = string, n = its length, loc = location in the inpit
 * - if s denotes a built-in operation, then we push the opcode
 *   otherwise, we push a generic version (e.g., MK_APPLY) if available.
 */

/*
 * Sort name
 */
void tstack_push_sort_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
}


/*
 * Symbol in an indexed sort
 * (_ <symbol> <number> ... <number> )
 */
void tstack_push_idx_sort(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
}


/*
 * Symbol as a sort cconstructor
 * (<symbol> <sort> .,, <sort>)
 */
void tstack_push_sort_constructor(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
}

/*
 * Symbol in an indexed sort constructor
 * ( (_ <symbol> <number> ... <number> ) <sort> ... <sort> )
 */
void tstack_push_idx_sort_constructor(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
}


/*
 * Term name (constant term)
 */
void tstack_push_term_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  
}


/*
 * Symbol in a function application
 *  ( <symbol> <term> ... <term> )
 */
void tstack_push_smt2_op(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
}


/*
 * Symbol in an indexed function application
 *  ( (_ <symbol> <number> ... <number> ) <term> ... <term> )
 */
void tstack_push_smt2_idx_op(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
}


/*
 * Symbol in an indexed term
 *  ( _ <symbol> <number> ... <number> )
 */
void tstack_push_idx_term(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {  
}







/*
 * SORT/TERM CONSTRUCTORS
 */

/*
 * Indexed stuff should all be eliminated so we just raise an exception
 * if any of these are called. That's because all indexed symbols are
 * defined in a theory (the user can't add new ones).
 */

/*
 * [indexed-sort <symbol> <numeral> ... <numeral> ]
 */
static void check_smt2_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {  
}


/*
 * [app-indexed-sort <symbol> <numeral> ... <numeral> <type> ... <type>]
 */
static void check_smt2_app_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_app_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [indexed-term <symbol> <numeral> ... <numeral> ]
 */
static void check_smt2_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [sorted-index-term <symbol> <numeral> ... <numeral> <type>]
 */
static void check_smt2_sorted_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_sorted_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [indexed-apply <symbol> <numeral> ... <numeral> ]
 */
static void check_smt2_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [sorted-index-apply <symbol> <numeral> ... <numeral> <type>]
 */
static void check_smt2_sorted_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_sorted_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}


/*
 * [sorted-term <symbol> <type>]
 */
static void check_smt2_sorted_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_sorted_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}



/*
 * [sorted-apply <symbol> <type>]
 */
static void check_smt2_sorted_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_sorted_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}



/*
 * Initialize stack for smt2:
 * - must be called after init_smt2
 */
void init_smt2_tstack(tstack_t *stack) {
  init_tstack(stack, NUM_SMT2_OPCODES);
  tstack_set_avtbl(stack, __smt2_globals.avtbl);

  tstack_add_op(stack, SMT2_EXIT, false, eval_smt2_exit, check_smt2_exit);
  tstack_add_op(stack, SMT2_GET_ASSERTIONS, false, eval_smt2_get_assertions, check_smt2_get_assertions);
  tstack_add_op(stack, SMT2_GET_ASSIGNMENT, false, eval_smt2_get_assignment, check_smt2_get_assignment);
  tstack_add_op(stack, SMT2_GET_PROOF, false, eval_smt2_get_proof, check_smt2_get_proof);
  tstack_add_op(stack, SMT2_GET_UNSAT_CORE, false, eval_smt2_get_unsat_core, check_smt2_get_unsat_core);
  tstack_add_op(stack, SMT2_GET_VALUE, false, eval_smt2_get_value, check_smt2_get_value);
  tstack_add_op(stack, SMT2_GET_OPTION, false, eval_smt2_get_option, check_smt2_get_option);
  tstack_add_op(stack, SMT2_GET_INFO, false, eval_smt2_get_info, check_smt2_get_info);
  tstack_add_op(stack, SMT2_SET_OPTION, false, eval_smt2_set_option, check_smt2_set_option);
  tstack_add_op(stack, SMT2_SET_INFO, false, eval_smt2_set_info, check_smt2_set_info);
  tstack_add_op(stack, SMT2_SET_LOGIC, false, eval_smt2_set_logic, check_smt2_set_logic);
  tstack_add_op(stack, SMT2_PUSH, false, eval_smt2_push, check_smt2_push);
  tstack_add_op(stack, SMT2_POP, false, eval_smt2_pop, check_smt2_pop);
  tstack_add_op(stack, SMT2_ASSERT, false, eval_smt2_assert, check_smt2_assert);
  tstack_add_op(stack, SMT2_CHECK_SAT, false, eval_smt2_check_sat, check_smt2_check_sat);
  tstack_add_op(stack, SMT2_DECLARE_SORT, false, eval_smt2_declare_sort, check_smt2_declare_sort);
  tstack_add_op(stack, SMT2_DEFINE_SORT, false, eval_smt2_define_sort, check_smt2_define_sort);
  tstack_add_op(stack, SMT2_DECLARE_FUN, false, eval_smt2_declare_fun, check_smt2_declare_fun);
  tstack_add_op(stack, SMT2_DEFINE_FUN, false, eval_smt2_define_fun, check_smt2_define_fun);
  tstack_add_op(stack, SMT2_MAKE_ATTR_LIST, false, eval_smt2_make_attr_list, check_smt2_make_attr_list);
  tstack_add_op(stack, SMT2_ADD_ATTRIBUTES, false, eval_smt2_add_attributes, check_smt2_add_attributes);
  tstack_add_op(stack, SMT2_INDEXED_SORT, false, eval_smt2_indexed_sort, check_smt2_indexed_sort);
  tstack_add_op(stack, SMT2_APP_INDEXED_SORT, false, eval_smt2_app_indexed_sort, check_smt2_app_indexed_sort);
  tstack_add_op(stack, SMT2_INDEXED_TERM, false, eval_smt2_indexed_term, check_smt2_indexed_term);
  tstack_add_op(stack, SMT2_SORTED_TERM, false, eval_smt2_sorted_term, check_smt2_sorted_term);
  tstack_add_op(stack, SMT2_SORTED_INDEXED_TERM, false, eval_smt2_sorted_indexed_term, check_smt2_sorted_indexed_term);
  tstack_add_op(stack, SMT2_INDEXED_APPLY, false, eval_smt2_indexed_apply, check_smt2_indexed_apply);
  tstack_add_op(stack, SMT2_SORTED_APPLY, false, eval_smt2_sorted_apply, check_smt2_sorted_apply);
  tstack_add_op(stack, SMT2_SORTED_INDEXED_APPLY, false, eval_smt2_sorted_indexed_apply, check_smt2_sorted_indexed_apply);
}
