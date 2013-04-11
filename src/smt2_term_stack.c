/*
 * OPERATIONS FOR SMT-LIB 2.0
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <string.h>

#include "yices.h"

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
 * Conversion keys: specify how to interpret a symbol
 *
 * NOTE: this works for now because the SMT2 symbols are all
 * in a single category (i.e., one key per symbol is enough).
 */
typedef enum smt2_key {
  SMT2_KEY_TYPE,         // type name
  SMT2_KEY_TYPE_OP,      // type constructor 
  SMT2_KEY_IDX_TYPE,     // indexed type
  SMT2_KEY_IDX_TYPE_OP,  // indexed type constructor

  SMT2_KEY_TERM,         // term name
  SMT2_KEY_TERM_OP,      // function name
  SMT2_KEY_IDX_TERM,     // indexed term
  SMT2_KEY_IDX_TERM_OP,  // indexed term constructor

  // special codes
  SMT2_KEY_IDX_BV,       // for bv<numeral> construct
  SMT2_KEY_ERROR_BV,     // for an invalid bv<xxx> (<xxx> not a numeral)
  SMT2_KEY_UNKNOWN,      // not a built-in symbol
} smt2_key_t;


/*
 * Conversion table:
 * - a symbol s can be converted to a type, a term, an opcode, 
 *   or something else. The conversion is determined by 
 *      smt2_key[s] = conversion key
 *      smt2_map[s] = conversion value (i.e., type, term, or opcode)
 *
 * - if key is KEY_TYPE then map is a type id
 * - if key is KEY_TERM then map is a term id
 * - if key is KEY_UNKNOWN or KEY_ERROR_BV then map is ignored
 * - otherwise map is an opcode
 *
 * For operations that Yices does not yet support, we set map to -1
 * (independent of the key).
 */
static const uint8_t smt2_key[NUM_SMT2_SYMBOLS] = {
  SMT2_KEY_TYPE,         // SMT2_SYM_BOOL
  SMT2_KEY_TERM,         // SMT2_SYM_TRUE
  SMT2_KEY_TERM,         // SMT2_SYM_FALSE
  SMT2_KEY_TERM_OP,      // SMT2_SYM_NOT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_IMPLIES
  SMT2_KEY_TERM_OP,      // SMT2_SYM_AND
  SMT2_KEY_TERM_OP,      // SMT2_SYM_OR
  SMT2_KEY_TERM_OP,      // SMT2_SYM_XOR
  SMT2_KEY_TERM_OP,      // SMT2_SYM_EQ
  SMT2_KEY_TERM_OP,      // SMT2_SYM_DISTINCT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_ITE
  SMT2_KEY_TYPE_OP,      // SMT2_SYM_ARRAY
  SMT2_KEY_TERM_OP,      // SMT2_SYM_SELECT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_STORE
  SMT2_KEY_TYPE,         // SMT2_SYM_INT
  SMT2_KEY_TYPE,         // SMT2_SYM_REAL
  SMT2_KEY_TERM_OP,      // SMT2_SYM_MINUS
  SMT2_KEY_TERM_OP,      // SMT2_SYM_PLUS
  SMT2_KEY_TERM_OP,      // SMT2_SYM_TIMES
  SMT2_KEY_TERM_OP,      // SMT2_SYM_DIVIDES
  SMT2_KEY_TERM_OP,      // SMT2_SYM_LE
  SMT2_KEY_TERM_OP,      // SMT2_SYM_LT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_GE
  SMT2_KEY_TERM_OP,      // SMT2_SYM_GT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_DIV
  SMT2_KEY_TERM_OP,      // SMT2_SYM_MOD
  SMT2_KEY_TERM_OP,      // SMT2_SYM_ABS
  SMT2_KEY_TERM_OP,      // SMT2_SYM_TO_REAL
  SMT2_KEY_TERM_OP,      // SMT2_SYM_TO_INT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_IS_INT
  SMT2_KEY_IDX_TERM_OP,  // SMT2_SYM_DIVISIBLE
  SMT2_KEY_IDX_BV,       // SMT2_SYM_BV_CONSTANT
  SMT2_KEY_IDX_TYPE,     // SMT2_SYM_BITVEC
  SMT2_KEY_TERM_OP,      // SMT2_SYM_CONCAT
  SMT2_KEY_IDX_TERM_OP,  // SMT2_SYM_EXTRACT
  SMT2_KEY_IDX_TERM_OP,  // SMT2_SYM_REPEAT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVCOMP
  SMT2_KEY_UNKNOWN,      // SMT2_SYM_BVREDOR (should not occur)
  SMT2_KEY_UNKNOWN,      // SMT2_SYM_BVREDAND (should not occur)
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVNOT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVAND
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVOR
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVNAND
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVNOR
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVXOR
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVXNOR
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVNEG
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVADD
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVSUB
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVMUL
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVUDIV
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVUREM
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVSDIV
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVSREM
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVSMOD
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVSHL
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVLSHR
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVASHR
  SMT2_KEY_IDX_TERM_OP,  // SMT2_SYM_ZERO_EXTEND
  SMT2_KEY_IDX_TERM_OP,  // SMT2_SYM_SIGN_EXTEND
  SMT2_KEY_IDX_TERM_OP,  // SMT2_SYM_ROTATE_LEFT
  SMT2_KEY_IDX_TERM_OP,  // SMT2_SYM_ROTATE_RIGHT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVULT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVULE
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVUGT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVUGE
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVSLT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVSLE
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVSGT
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVSGE
  SMT2_KEY_ERROR_BV,     // SMT2_SYM_INVALID_BV_CONSTANT
  SMT2_KEY_UNKNOWN,      // SMT2_SYM_UNKNOWN
};

static const int32_t smt2_val[NUM_SMT2_SYMBOLS] = {
  bool_id,               // SMT2_SYM_BOOL (in types.h)
  true_term,             // SMT2_SYM_TRUE (in terms.h)
  false_term,            // SMT2_SYM_FALSE (in terms.h)
  MK_NOT,                // SMT2_SYM_NOT
  MK_IMPLIES,            // SMT2_SYM_IMPLIES
  MK_AND,                // SMT2_SYM_AND
  MK_OR,                 // SMT2_SYM_OR
  MK_XOR,                // SMT2_SYM_XOR
  MK_EQ,                 // SMT2_SYM_EQ
  MK_DISTINCT,           // SMT2_SYM_DISTINCT
  MK_ITE,                // SMT2_SYM_ITE
  SMT2_MK_ARRAY,         // SMT2_SYM_ARRAY
  SMT2_MK_SELECT,        // SMT2_SYM_SELECT
  SMT2_MK_STORE,         // SMT2_SYM_STORE
  int_id,                // SMT2_SYM_INT
  real_id,               // SMT2_SYM_REAL
  MK_SUB,                // SMT2_SYM_MINUS
  MK_ADD,                // SMT2_SYM_PLUS
  MK_MUL,                // SMT2_SYM_TIMES
  MK_DIVISION,           // SMT2_SYM_DIVIDES
  MK_LE,                 // SMT2_SYM_LE
  MK_LT,                 // SMT2_SYM_LT
  MK_GE,                 // SMT2_SYM_GE
  MK_GT,                 // SMT2_SYM_GT
  -1,                    // SMT2_SYM_DIV (integer division not supported)
  -1,                    // SMT2_SYM_MOD 
  -1,                    // SMT2_SYM_ABS
  -1,                    // SMT2_SYM_TO_REAL (?? could use a NO_OP for that one)
  -1,                    // SMT2_SYM_TO_INT
  -1,                    // SMT2_SYM_IS_INT
  -1,                    // SMT2_SYM_DIVISIBLE
  MK_BV_CONST,           // SMT2_SYM_BV_CONSTANT ( for _bv<value> size)
  MK_BV_TYPE,            // SMT2_SYM_BITVEC
  MK_BV_CONCAT,          // SMT2_SYM_CONCAT
  MK_BV_EXTRACT,         // SMT2_SYM_EXTRACT
  MK_BV_REPEAT,          // SMT2_SYM_REPEAT
  MK_BV_COMP,            // SMT2_SYM_BVCOMP
  MK_BV_REDOR,           // SMT2_SYM_BVREDOR (should not occur)
  MK_BV_REDAND,          // SMT2_SYM_BVREDAND
  MK_BV_NOT,             // SMT2_SYM_BVNOT
  MK_BV_AND,             // SMT2_SYM_BVAND
  MK_BV_OR,              // SMT2_SYM_BVOR
  MK_BV_NAND,            // SMT2_SYM_BVNAND
  MK_BV_NOR,             // SMT2_SYM_BVNOR
  MK_BV_XOR,             // SMT2_SYM_BVXOR
  MK_BV_XNOR,            // SMT2_SYM_BVXNOR
  MK_BV_NEG,             // SMT2_SYM_BVNEG
  MK_BV_ADD,             // SMT2_SYM_BVADD
  MK_BV_SUB,             // SMT2_SYM_BVSUB
  MK_BV_MUL,             // SMT2_SYM_BVMUL
  MK_BV_DIV,             // SMT2_SYM_BVUDIV
  MK_BV_REM,             // SMT2_SYM_BVUREM
  MK_BV_SDIV,            // SMT2_SYM_BVSDIV
  MK_BV_SREM,            // SMT2_SYM_BVSREM
  MK_BV_SMOD,            // SMT2_SYM_BVSMOD
  MK_BV_SHL,             // SMT2_SYM_BVSHL
  MK_BV_LSHR,            // SMT2_SYM_BVLSHR
  MK_BV_ASHR,            // SMT2_SYM_BVASHR
  MK_BV_ZERO_EXTEND,     // SMT2_SYM_ZERO_EXTEND
  MK_BV_SIGN_EXTEND,     // SMT2_SYM_SIGN_EXTEND
  MK_BV_ROTATE_LEFT,     // SMT2_SYM_ROTATE_LEFT
  MK_BV_ROTATE_RIGHT,    // SMT2_SYM_ROTATE_RIGHT
  MK_BV_LT,              // SMT2_SYM_BVULT
  MK_BV_LE,              // SMT2_SYM_BVULE
  MK_BV_GT,              // SMT2_SYM_BVUGT
  MK_BV_GE,              // SMT2_SYM_BVUGE
  MK_BV_SLT,             // SMT2_SYM_BVSLT
  MK_BV_SLE,             // SMT2_SYM_BVSLE
  MK_BV_SGT,             // SMT2_SYM_BVSGT
  MK_BV_SGE,             // SMT2_SYM_BVSGE
  NO_OP,                 // SMT2_SYM_INVALID_BV_CONSTANT (ignored)
  NO_OP,                 // SMT2_SYM_UNKNOWN (ignored)
};


/*
 * Sort name
 */
void tstack_push_sort_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
  case SMT2_KEY_TYPE:
    tstack_push_type(stack, smt2_val[symbol], loc);
    break;

  case SMT2_KEY_UNKNOWN:
    tstack_push_type_by_name(stack, s, loc);
    break;

  default:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_SORT);
    break;
  }
}


/*
 * Symbol in an indexed sort
 * (_ <symbol> <number> ... <number> )
 */
void tstack_push_idx_sort(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
  case SMT2_KEY_IDX_TYPE:
    tstack_push_op(stack, smt2_val[symbol], loc);
    break;

  case SMT2_KEY_UNKNOWN:
    push_exception(stack, loc, s, SMT2_UNDEF_IDX_SORT);
    break;

  default:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_IDX_SORT);
    break;
  }
}


/*
 * Symbol as a sort cconstructor
 * (<symbol> <sort> .,, <sort>)
 */
void tstack_push_sort_constructor(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
  case SMT2_KEY_TYPE_OP:
    tstack_push_op(stack, smt2_val[symbol], loc);
    break;

  case SMT2_KEY_UNKNOWN:
    tstack_push_macro_by_name(stack, s, loc);
    break;

  default:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_SORT_OP);
    break;
  }
}


/*
 * Symbol in an indexed sort constructor
 * ( (_ <symbol> <number> ... <number> ) <sort> ... <sort> )
 */
void tstack_push_idx_sort_constructor(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
  case SMT2_KEY_IDX_TYPE_OP:
    tstack_push_op(stack, smt2_val[symbol], loc);
    break;

  case SMT2_KEY_UNKNOWN:
    push_exception(stack, loc, s, SMT2_UNDEF_IDX_SORT_OP);
    break;

  default:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_IDX_SORT_OP);
    break;
  }
}


/*
 * Term name (constant term)
 */
void tstack_push_term_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
  case SMT2_KEY_TERM:
    tstack_push_term(stack, smt2_val[symbol], loc);
    break;

  case SMT2_KEY_UNKNOWN:
    tstack_push_term_by_name(stack, s, loc);
    break;

  default:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_TERM);
    break;
  }  
}


/*
 * Symbol in a function application
 *  ( <symbol> <term> ... <term> )
 */
void tstack_push_smt2_op(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
  case SMT2_KEY_TERM_OP:
    tstack_push_op(stack, smt2_val[symbol], loc);
    break;

  case SMT2_KEY_UNKNOWN:
    // uninterprted function
    tstack_push_op(stack, MK_APPLY, loc);
    tstack_push_term_by_name(stack, s, loc);
    break;

  default:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_FUNCTION);
    break;
  }
}


/*
 * Symbol in an indexed function application
 *  ( (_ <symbol> <number> ... <number> ) <term> ... <term> )
 */
void tstack_push_smt2_idx_op(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
  case SMT2_KEY_IDX_TERM_OP:
    tstack_push_op(stack, smt2_val[symbol], loc);
    break;

  case SMT2_KEY_UNKNOWN:
    push_exception(stack, loc, s, SMT2_UNDEF_IDX_FUNCTION);
    break;

  default:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_IDX_FUNCTION);
    break;
  }
}


/*
 * Symbol in an indexed term
 *  ( _ <symbol> <number> ... <number> )
 */
void tstack_push_idx_term(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
  case SMT2_KEY_IDX_TERM:
    tstack_push_op(stack, smt2_val[symbol], loc);
    break;

  case SMT2_KEY_IDX_BV:
    // s is bv<numeral> and is to be interpreted as (mk-bv <numeral> ...)
    assert(n > 2);
    tstack_push_op(stack, MK_BV_CONST, loc);
    tstack_push_rational(stack, s + 2, loc); // skip the 'bv' prefix
    break;

  case SMT2_KEY_ERROR_BV:
    // s is bv0<xxx>: invalid bv<numeral>
    push_exception(stack, loc, s, SMT2_INVALID_IDX_BV);
    break;

  case SMT2_KEY_UNKNOWN:
    push_exception(stack, loc, s, SMT2_UNDEF_IDX_TERM);
    break;

  default:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_IDX_TERM);
    break;
  }
}


/*
 * ARRAY-THEORY
 */

static void check_term(tstack_t *stack, term_t t) {
  if (t == NULL_TERM) report_yices_error(stack);
}

/*
 * [mk-array <sort1> <sort2> ] --> turned to function from <sort1> to <sort2>
 */
static void check_smt2_mk_array(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_MK_ARRAY);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_TYPE);
  check_tag(stack, f+1, TAG_TYPE);
}

static void eval_smt2_mk_array(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  type_t dom, range, tau;

  dom = f[0].val.type;
  range = f[1].val.type;
  tau = yices_function_type(1, &dom, range);

  assert(tau != NULL_TYPE);
  tstack_pop_frame(stack);
  set_type_result(stack, tau);
}


/*
 * [select <array> <index> ] --> converted to (apply <array> <index> )
 */
static void check_smt2_mk_select(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_MK_SELECT);
  check_size(stack, n == 2);
}

static void eval_smt2_mk_select(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t array, index, t;

  array = get_term(stack, f);
  index = get_term(stack, f+1);
  t = yices_application(array, 1, &index);
  check_term(stack, t);

  tstack_pop_frame(stack);
  set_term_result(stack, t);  
}


/*
 * [store <array> <index> <value> ] --> converted to (update <array> <index> <value> )
 */
static void check_smt2_mk_store(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_MK_STORE);
  check_size(stack, n == 3);
}

static void eval_smt2_mk_store(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t array, index, value, t;

  array = get_term(stack, f);
  index = get_term(stack, f+1);
  value = get_term(stack, f+2);
  t = yices_update(array, 1, &index, value);
  check_term(stack, t);

  tstack_pop_frame(stack);
  set_term_result(stack, t);
}


/*
 * SORT CONSTRUCTORS
 */

/*
 * Indexed symbol should all be eliminated so we just raise an
 * exception if any of the indexed_sort/term/appl are called. That's
 * because all indexed symbols are defined in a theory (the user can't
 * add new ones).
 */

/*
 * [indexed-sort <symbol> <numeral> ... <numeral> ]
 */
static void check_smt2_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {  
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}


/*
 * [app-indexed-sort <symbol> <numeral> ... <numeral> <type> ... <type>]
 */
static void check_smt2_app_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_app_indexed_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}


/*
 * [indexed-term <symbol> <numeral> ... <numeral> ]
 */
static void check_smt2_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}


/*
 * [sorted-index-term <symbol> <numeral> ... <numeral> <type>]
 */
static void check_smt2_sorted_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_sorted_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}


/*
 * [indexed-apply <symbol> <numeral> ... <numeral> ]
 */
static void check_smt2_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}


/*
 * [sorted-index-apply <symbol> <numeral> ... <numeral> <type>]
 */
static void check_smt2_sorted_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_sorted_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
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
  tstack_add_op(stack, SMT2_MK_ARRAY, false, eval_smt2_mk_array, check_smt2_mk_array);
  tstack_add_op(stack, SMT2_MK_SELECT, false, eval_smt2_mk_select, check_smt2_mk_select);
  tstack_add_op(stack, SMT2_MK_STORE, false, eval_smt2_mk_store, check_smt2_mk_store);
  tstack_add_op(stack, SMT2_INDEXED_SORT, false, eval_smt2_indexed_sort, check_smt2_indexed_sort);
  tstack_add_op(stack, SMT2_APP_INDEXED_SORT, false, eval_smt2_app_indexed_sort, check_smt2_app_indexed_sort);
  tstack_add_op(stack, SMT2_INDEXED_TERM, false, eval_smt2_indexed_term, check_smt2_indexed_term);
  tstack_add_op(stack, SMT2_SORTED_TERM, false, eval_smt2_sorted_term, check_smt2_sorted_term);
  tstack_add_op(stack, SMT2_SORTED_INDEXED_TERM, false, eval_smt2_sorted_indexed_term, check_smt2_sorted_indexed_term);
  tstack_add_op(stack, SMT2_INDEXED_APPLY, false, eval_smt2_indexed_apply, check_smt2_indexed_apply);
  tstack_add_op(stack, SMT2_SORTED_APPLY, false, eval_smt2_sorted_apply, check_smt2_sorted_apply);
  tstack_add_op(stack, SMT2_SORTED_INDEXED_APPLY, false, eval_smt2_sorted_indexed_apply, check_smt2_sorted_indexed_apply);
}
