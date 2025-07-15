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
 * OPERATIONS FOR SMT-LIB 2.0
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <string.h>

#include "api/yices_extensions.h"
#include "api/yices_api_lock_free.h"
#include "api/yices_globals.h"
#include "frontend/smt2/attribute_values.h"
#include "frontend/smt2/smt2_commands.h"
#include "frontend/smt2/smt2_lexer.h"
#include "frontend/smt2/smt2_term_stack.h"
#include "parser_utils/tstack_internals.h"

#include "yices.h"


/*
 * Convert element e to an attribute value
 * - raise exception INTERNAL_ERROR if that can't be done
 */
static aval_t get_aval(tstack_t *stack, stack_elem_t *e) {
  aval_t v;

  assert(stack->avtbl != NULL);

  switch (e->tag) {
  case TAG_SYMBOL:
    v = attr_vtbl_symbol(stack->avtbl, e->val.string);
    break;

  case TAG_STRING:
    v = attr_vtbl_string(stack->avtbl, e->val.string);
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
 * Check whether element e is an smt2_keyword
 */
static bool is_keyword(stack_elem_t *e) {
  return e->tag == TAG_SYMBOL && smt2_string_is_keyword(e->val.string);
}


/*
 * Convert element e into an smt2_keyword
 * - raise exception INTERNAL_ERROR if e is not a keyword
 */
static smt2_keyword_t get_keyword(tstack_t *stack, stack_elem_t *e) {
  uint32_t len;

  if (! is_keyword(e)) {
    raise_exception(stack, e, TSTACK_INTERNAL_ERROR);
  }

  len = strlen(e->val.string);
  return smt2_string_to_keyword(e->val.string, len);
}


/*
 * Check whether t is a valid term
 */
static void check_term(tstack_t *stack, term_t t) {
  if (t == NULL_TERM) report_yices_error(stack);
}



/*
 * Check whether a stack element is an integer term
 * - raise exception SMT2_TERM_NOT_INTEGER if not
 */
static void check_integer_term(tstack_t *stack, stack_elem_t *e) {
  rational_t *q;
  rba_buffer_t *b;
  term_t t;

  switch (e->tag) {
  case TAG_RATIONAL:
    q = &e->val.rational;
    if (!q_is_integer(q)) {
      raise_exception(stack, e, SMT2_TERM_NOT_INTEGER);
    }
    break;

  case TAG_TERM:
  case TAG_SPECIAL_TERM:
    t = e->val.term;
    if (! is_integer_term(__yices_globals.terms, t)) {
      raise_exception(stack, e, SMT2_TERM_NOT_INTEGER);
    }
    break;

  case TAG_ARITH_BUFFER:
    b = e->val.arith_buffer;
    if (! arith_poly_is_integer(__yices_globals.terms, b)) {
      raise_exception(stack, e, SMT2_TERM_NOT_INTEGER);
    }
    break;

  default:
    raise_exception(stack, e, SMT2_TERM_NOT_INTEGER);
    break;
  }
}






/*
 * MODIFIED OPCODES
 */

/*
 * 1) mk_implies can take more than two arguments
 *    (=> a b c) is interpreted as (=> a (=> b c))
 *
 * 2) chainable operators:
 *    core: =
 *    arithmetic: <=, <, >=, >
 *
 * 3) missing operators: div, mod, abs, divisible
 *    note: div is marked as left-associative!
 *    (div a b c) is interpreted as (div (div a b) c)
 *
 * 4) restrictions on bvnand, bvnor, bvxnor
 *
 * 5) n-ary division
 */

/*
 * (_ bv<xx> n) is mapped to [mk-bv-const xx n]
 * - xx is the value, n is the number of bits
 * - this is the opposite order of Yices (i.e.. [mk-bv-const n xx])
 */
static void check_smt2_mk_bv_const(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_CONST);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_RATIONAL);
  check_tag(stack, f+1, TAG_RATIONAL);
}

static void eval_smt2_mk_bv_const(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t size;
  rational_t *val;

  size = get_integer(stack, f+1);
  val = &f[0].val.rational;
  mk_bv_const_core(stack, f, size, val);
}


/*
 * ((_ rotate_left i)  bv) is mapped to [mk-rotate-left i bv]
 * - the default mk-rotate-left expect arguments in the other order
 */
static void check_smt2_mk_bv_rotate_left(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_ROTATE_LEFT);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_RATIONAL);
}

static void eval_smt2_mk_bv_rotate_left(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t index;
  bvlogic_buffer_t *b;

  index = get_integer(stack, f);
  b = tstack_get_bvlbuffer(stack);
  bvl_set_elem(stack, b, f+1);
  if (! yices_check_smt2_rotate(b, &index)) {
    report_yices_error(stack);
  }
  // we known 0 <= index <= bitsize of b
  bvlogic_buffer_rotate_left(b, index);

  tstack_pop_frame(stack);
  set_bvlogic_result(stack, b);
}


/*
 * ((_ rotate_right i)  bv) is mapped to [mk-rotate-right i bv]
 * - the default mk-rotate-left expect arguments in the other order
 */
static void check_smt2_mk_bv_rotate_right(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_ROTATE_RIGHT);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_RATIONAL);
}

static void eval_smt2_mk_bv_rotate_right(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t index;
  bvlogic_buffer_t *b;

  index = get_integer(stack, f);
  b = tstack_get_bvlbuffer(stack);
  bvl_set_elem(stack, b, f+1);
  if (! yices_check_smt2_rotate(b, &index)) {
    report_yices_error(stack);
  }
  // we known 0 <= index < bitsize of b
  bvlogic_buffer_rotate_right(b, index);

  tstack_pop_frame(stack);
  set_bvlogic_result(stack, b);
}


/*
 * ((_ repeat i) bv) is mapped to [mk-bv-repeat <rational> <bv>]
 */
static void check_smt2_mk_bv_repeat(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_REPEAT);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_RATIONAL);
}

static void eval_smt2_mk_bv_repeat(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t i;
  bvlogic_buffer_t *b;

  i = get_integer(stack, f);
  b = tstack_get_bvlbuffer(stack);
  bvl_set_elem(stack, b, f+1);

  // check for overflow or for i <= 0
  if (! yices_check_bvrepeat(b, i)) {
    report_yices_error(stack);
  }
  bvlogic_buffer_repeat_concat(b, i);
  tstack_pop_frame(stack);
  set_bvlogic_result(stack, b);
}


/*
 * ((_ sign_extend i) bv) is mapped to [mk-bv-sign-extend <rational> <bv>]
 */
static void check_smt2_mk_bv_sign_extend(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_SIGN_EXTEND);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_RATIONAL);
}

static void eval_smt2_mk_bv_sign_extend(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  mk_bv_sign_extend_core(stack, f+1, f);
}


/*
 * ((_ zero_extend i) bv) is mapped to [mk-bv-zero-extend <rational> <bv>]
 */
static void check_smt2_mk_bv_zero_extend(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_ZERO_EXTEND);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_RATIONAL);
}

static void eval_smt2_mk_bv_zero_extend(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  mk_bv_zero_extend_core(stack, f+1, f);
}


/*
 * n-ary implies: convert (=> t1 .... t_{n-1} t_n) to
 * (=> (and t1 ... t_{n-1}) t_n)
 */
static void check_smt2_mk_implies(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_IMPLIES);
  check_size(stack, n >= 2);
}

static void eval_smt2_mk_implies(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t *arg, left, right, t;
  uint32_t i;

  if (n == 2) {
    left = get_term(stack, f);
    right = get_term(stack, f+1);
  } else {
    n --;
    arg = get_aux_buffer(stack, n);
    for (i=0; i<n; i++) {
      arg[i] = get_term(stack, f+i);
    }
    left = yices_and(n, arg);
    right = get_term(stack, f+n);
  }

  t = yices_implies(left, right);
  check_term(stack, t);

  tstack_pop_frame(stack);
  set_term_result(stack, t);
}


/*
 * bvnand, bvnor, bvxnor:
 *
 * In the default implementation (term_stack2.c), we use the following rules
 *   (bvnand x_1 ... x_n) = (bvnot (bvand x_1 ... x_n))
 *   (bvnor x_1 ... x_n)  = (bvnot (bvor x_1 ... x_n))
 *   (bvxnor x_1 ... x_n) = (bvnot (bvxor x_1 ... x_n))
 *
 * In SMT-LIB2, we want to limit them to two arguments only. CVC4 and z3 use
 * this rule for bvxnor
 *   (bxnor x_1 x_2 x_3) = (bvxnor (bvxnor x1 x2) x3)
 * The standard says that bvxnor is not associatived.
 *
 * To be safe, we restrict bvnand, bvnor, bvxnor to exactly two arguments here.
 */

/*
 * [mk-bv-nand <bv> <bv>]
 */
static void check_smt2_mk_bv_nand(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_NAND);
  check_size(stack, n == 2);
}

static void eval_smt2_mk_bv_nand(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  bvlogic_buffer_t *b;

  b = tstack_get_bvlbuffer(stack);
  bvl_set_elem(stack, b, f);
  bvand_elem(stack, b, f+1);
  bvlogic_buffer_not(b);
  tstack_pop_frame(stack);
  set_bvlogic_result(stack, b);
}


/*
 * [mk-bv-nor <bv> <bv>]
 */
static void check_smt2_mk_bv_nor(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_NOR);
  check_size(stack, n == 2);
}

static void eval_smt2_mk_bv_nor(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  bvlogic_buffer_t *b;

  b = tstack_get_bvlbuffer(stack);
  bvl_set_elem(stack, b, f);
  bvor_elem(stack, b, f+1);
  bvlogic_buffer_not(b);
  tstack_pop_frame(stack);
  set_bvlogic_result(stack, b);
}


/*
 * [mk-bv-xnor <bv> <bv>]
 */
static void check_smt2_mk_bv_xnor(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_XNOR);
  check_size(stack, n == 2);
}

static void eval_smt2_mk_bv_xnor(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  bvlogic_buffer_t *b;

  b = tstack_get_bvlbuffer(stack);
  bvl_set_elem(stack, b, f);
  bvxor_elem(stack, b, f+1);
  bvlogic_buffer_not(b);
  tstack_pop_frame(stack);
  set_bvlogic_result(stack, b);
}




/*
 * CHAINABLE OPERATORS
 */

/*
 * smt_eq: can take more than two arguments;
 * we rewrite [mk-eq t1 ... t_n] to (and (eq t1 t_n) .... (eq t_{n-1} t_n))
 */
static void check_smt2_mk_eq(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_EQ);
  check_size(stack, n >= 2);
}

static void eval_smt2_mk_eq(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t *arg, last, first, t;
  uint32_t i;

  if (n == 2) {
    first = get_term(stack, f);
    last = get_term(stack, f+1);
    t = yices_eq(first, last);
  } else {
    arg = get_aux_buffer(stack, n);
    n --;
    last = get_term(stack, f+n);
    for (i=0; i<n; i++) {
      t = yices_eq(get_term(stack, f+i), last);
      check_term(stack, t);
      arg[i] = t;
    }
    t = yices_and(n, arg);
  }
  check_term(stack, t);

  tstack_pop_frame(stack);
  set_term_result(stack, t);
}



/*
 * Arithmetic comparisons are all chainable.
 * For example,  (< t1 t2 ... t_n) is (and (< t1 t2) (< t2 t3)  ... (< t_{n-1} t_n))
 */

// [mk-ge t1 .... t_n]
static void check_smt2_mk_ge(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_GE);
  check_size(stack, n >= 2);
}

// auxiliary function: build ge(f, f+1)
static term_t mk_binary_ge(tstack_t *stack, stack_elem_t *f) {
  rba_buffer_t *b;
  term_t t;

  b = tstack_get_abuffer(stack);
  add_elem(stack, b, f);
  sub_elem(stack, b, f+1);
  t = arith_buffer_get_geq0_atom(b); // [f] - [f+1] >= 0
  assert(t != NULL_TERM);

  return t;
}

static void eval_smt2_mk_ge(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t *arg, t;
  uint32_t i;

  if (n == 2) {
    t = mk_binary_ge(stack, f);
  } else {
    n --;
    arg = get_aux_buffer(stack, n);
    for (i=0; i<n; i++) {
      arg[i] = mk_binary_ge(stack, f+i);
    }
    t = yices_and(n, arg);
  }
  check_term(stack, t);

  tstack_pop_frame(stack);
  set_term_result(stack, t);
}


// [mk-gt t1 ... t_n]
static void check_smt2_mk_gt(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_GT);
  check_size(stack, n >= 2);
}

// auxiliary function: build ge(f, f+1)
static term_t mk_binary_gt(tstack_t *stack, stack_elem_t *f) {
  rba_buffer_t *b;
  term_t t;

  b = tstack_get_abuffer(stack);
  add_elem(stack, b, f);
  sub_elem(stack, b, f+1);
  t = arith_buffer_get_gt0_atom(b); // [f] - [f+1] >= 0
  assert(t != NULL_TERM);

  return t;
}

static void eval_smt2_mk_gt(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t *arg, t;
  uint32_t i;

  if (n == 2) {
    t = mk_binary_gt(stack, f);
  } else {
    n --;
    arg = get_aux_buffer(stack, n);
    for (i=0; i<n; i++) {
      arg[i] = mk_binary_gt(stack, f+i);
    }
    t = yices_and(n, arg);
  }
  check_term(stack, t);

  tstack_pop_frame(stack);
  set_term_result(stack, t);
}



// [mk-le t1 ... t_n]
static void check_smt2_mk_le(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_LE);
  check_size(stack, n >= 2);
}

// auxiliary function: build le(f, f+1)
static term_t mk_binary_le(tstack_t *stack, stack_elem_t *f) {
  rba_buffer_t *b;
  term_t t;

  b = tstack_get_abuffer(stack);
  add_elem(stack, b, f);
  sub_elem(stack, b, f+1);
  t = arith_buffer_get_leq0_atom(b); // [f] - [f+1] >= 0
  assert(t != NULL_TERM);

  return t;
}

static void eval_smt2_mk_le(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t *arg, t;
  uint32_t i;

  if (n == 2) {
    t = mk_binary_le(stack, f);
  } else {
    n --;
    arg = get_aux_buffer(stack, n);
    for (i=0; i<n; i++) {
      arg[i] = mk_binary_le(stack, f+i);
    }
    t = yices_and(n, arg);
  }
  check_term(stack, t);

  tstack_pop_frame(stack);
  set_term_result(stack, t);
}


// [mk-lt t1 ... t_n]
static void check_smt2_mk_lt(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_LT);
  check_size(stack, n >= 2);
}

// auxiliary function: build ge(f, f+1)
static term_t mk_binary_lt(tstack_t *stack, stack_elem_t *f) {
  rba_buffer_t *b;
  term_t t;

  b = tstack_get_abuffer(stack);
  add_elem(stack, b, f);
  sub_elem(stack, b, f+1);
  t = arith_buffer_get_lt0_atom(b); // [f] - [f+1] >= 0
  assert(t != NULL_TERM);

  return t;
}

static void eval_smt2_mk_lt(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t *arg, t;
  uint32_t i;

  if (n == 2) {
    t = mk_binary_lt(stack, f);
  } else {
    n --;
    arg = get_aux_buffer(stack, n);
    for (i=0; i<n; i++) {
      arg[i] = mk_binary_lt(stack, f+i);
    }
    t = yices_and(n, arg);
  }
  check_term(stack, t);

  tstack_pop_frame(stack);
  set_term_result(stack, t);
}




/*
 * NEW OPERATORS FOR MIXED AND INTEGER ARITHMETIC.
 */

/*
 * [to_real x]: x must be an integer. We treat this operation as a no-op.
 */
static void check_smt2_to_real(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_MK_TO_REAL);
  check_size(stack, n == 1);
  check_integer_term(stack, f);

  //  fprintf(stderr, "to_real\n");
}

static void eval_smt2_to_real(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  copy_result_and_pop_frame(stack, f);
}


/*
 * [to_int x] (is the same as (floor x)
 */
static void check_smt2_to_int(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_MK_TO_INT);
  check_size(stack, n == 1);

  //  fprintf(stderr, "to_int\n");
}

static void eval_smt2_to_int(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t t;

  t = get_term(stack, f);
  t = yices_floor(t);
  check_term(stack, t);

  tstack_pop_frame(stack);
  set_term_result(stack, t);
}


/*
 * [is_int x]
 */
static void check_smt2_is_int(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_MK_IS_INT);
  check_size(stack, n == 1);

  //  fprintf(stderr, "is_int\n");
}

static void eval_smt2_is_int(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t t;

  t = get_term(stack, f);
  t = yices_is_int_atom(t);
  check_term(stack, t);

  tstack_pop_frame(stack);
  set_term_result(stack, t);
}


/*
 * [abs x]
 *
 * In SMTLIB2, (abs x) is defined only for integers. We don't check for this,
 * and we accept (abs x) for any arithmetic x.
 */
static void check_smt2_abs(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_MK_ABS);
  check_size(stack, n == 1);
}

static void eval_smt2_abs(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t t;

  t = get_term(stack, f);
  t = yices_abs(t);
  check_term(stack, t);

  tstack_pop_frame(stack);
  set_term_result(stack, t);

  //  fprintf(stderr, "abs\n");
}


/*
 * [div x y]
 * - y must be a non-zero constant
 *
 * In SMTLIB2, both x and y should be integers. We accept reals too.
 *
 * Also, in SMTLIB2, it's allowed to write (div x1 x2 ... x_n).
 * That's interpreted as ((..(div (div x1 x2) x3)... x_n)).
 */
static void check_smt2_div(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_MK_DIV);
  check_size(stack, n >= 2);
}

static void eval_smt2_div(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t t1, t2;
  uint32_t i;

  t1 = get_term(stack, f);
  for (i=1; i<n; i++) {
    t2 = get_term(stack, f+i);
    t1 = yices_idiv(t1, t2);
    check_term(stack, t1);
  }

  tstack_pop_frame(stack);
  set_term_result(stack, t1);
}


/*
 * [mod x y]
 * - y must be a non-zero constant
 *
 * In SMTLIB2, both x and y should be integers. We accept reals too.
 */
static void check_smt2_mod(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_MK_MOD);
  check_size(stack, n == 2);
}

static void eval_smt2_mod(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t t1, t2, t;

  t1 = get_term(stack, f);
  t2 = get_term(stack, f+1);
  t = yices_imod(t1, t2);
  check_term(stack, t);
  
  tstack_pop_frame(stack);
  set_term_result(stack, t);
}


/*
 * [divisible x y] (i.e.,  whether y is a multiple of x)
 * - x must be a constant
 *
 * In SMTLIB2, both x and y should be integers. We accept reals too.
 */
static void check_smt2_divisible(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_MK_DIVISIBLE);
  check_size(stack, n == 2);
}

static void eval_smt2_divisible(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t t1, t2, t;

  t1 = get_term(stack, f);
  t2 = get_term(stack, f+1);
  t = yices_divides_atom(t1, t2);
  check_term(stack, t);
  
  tstack_pop_frame(stack);
  set_term_result(stack, t);
}


/*
 * n-ary division: [/ x1 x2 ... xn]
 *
 * This is interpreted as left-associative:
 * (/ a b c) is (/ (/ a b) c)
 *
 * We rewrite this to (/ a (* b c))
 */
static void check_smt2_mk_division(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_DIVISION);
  check_size(stack, n >= 2);
}

/*
 * Auxiliary function: compute the divisor = product f[0] x ... x f[n-1]
 * If the divisor is a non-zero rational, it is returned in d and the function
 * returns NULL_TERM
 * Otherwise, the function leaves d unchanged and returns a term equal to the divisor
 */
static term_t make_divisor_product(tstack_t *stack, stack_elem_t *f, uint32_t n, rational_t *d) {
  rba_buffer_t *b;
  mono_t *m;
  uint32_t i;
  term_t t;

  assert(n >= 1);

  t = NULL_TERM;
  if (n == 1) {
    if (elem_is_nz_constant(f, d)) {
      assert(q_is_nonzero(d));
    } else {
      t = get_term(stack, f);
    }
  } else {
    // compute the product f[0] x ... x f[n-1]
    b = yices_new_arith_buffer();
    assert(rba_buffer_is_zero(b));

    // note: this loop may fail and call longjmp
    // but the buffer b will be deleted on a call to yices_exit
    // so there's no risk of memory leak.
    add_elem(stack, b, f);
    for (i=1; i<n; i++) {
      mul_elem(stack, b, f+i);
    }

    if (rba_buffer_is_nonzero(b)) {
      // b is a non-zero constant
      m = rba_buffer_get_constant_mono(b);
      assert(m != NULL);
      q_set(d, &m->coeff);
      assert(q_is_nonzero(d));
    } else {
      t = arith_buffer_get_term(b);
    }
    yices_free_arith_buffer(b);
  }

  return t;
}

static void eval_smt2_mk_division(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  rba_buffer_t *b;
  rational_t divider;
  term_t t1, t2, t;

  assert(n >= 2);

  q_init(&divider);
  t2 = make_divisor_product(stack, f+1, n-1, &divider);
  if (t2 == NULL_TERM) {
    // division by a constant
    assert(q_is_nonzero(&divider));
    if (f->tag == TAG_RATIONAL) {
      q_div(&f->val.rational, &divider);
      copy_result_and_pop_frame(stack, f);
    } else {
      b = tstack_get_abuffer(stack);
      add_elem(stack, b, f);
      rba_buffer_div_const(b, &divider);
      tstack_pop_frame(stack);
      set_arith_result(stack, b);
    }
  } else {
    // the divisor is t2
    t1 = get_term(stack, f);
    t = _o_yices_division(t1, t2);
    check_term(stack, t);
    tstack_pop_frame(stack);
    set_term_result(stack,  t);
  }

  /*
   * It's safe to clear the divider only here.
   * If the code above raises an exception, divider is still 0/1
   * and q_clear would do nothing anyway.
   */
  q_clear(&divider);
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
 * [silent-exit]
 */
static void check_smt2_silent_exit(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_SILENT_EXIT);
  check_size(stack, n == 0);
}

static void eval_smt2_silent_exit(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_silent_exit();
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
 * [get-unsat_assumptions]
 */
static void check_smt2_get_unsat_assumptions(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_GET_UNSAT_ASSUMPTIONS);
  check_size(stack, n == 0);
}

static void eval_smt2_get_unsat_assumptions(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_get_unsat_assumptions();
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [get-unsat-model-interpolant]
 */
static void check_smt2_get_unsat_model_interpolant(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_GET_UNSAT_MODEL_INTERPOLANT);
  check_size(stack, n == 0);
}

static void eval_smt2_get_unsat_model_interpolant(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_get_unsat_model_interpolant();
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
  smt2_get_option(f[0].val.string);
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
  smt2_get_info(f[0].val.string);
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

  if (n == 1) {
    smt2_set_option(f[0].val.string, AVAL_NULL);
  } else {
    v = get_aval(stack, f+1);
    aval_incref(stack->avtbl, v);
    smt2_set_option(f[0].val.string, v);
    aval_decref(stack->avtbl, v);
  }
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

  if (n == 1) {
    smt2_set_info(f[0].val.string, AVAL_NULL);
  } else {
    v = get_aval(stack, f+1);
    aval_incref(stack->avtbl, v);
    smt2_set_info(f[0].val.string, v);
    aval_decref(stack->avtbl, v);
  }
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
  smt2_set_logic(f[0].val.string);
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
  check_op(stack, SMT2_POP);
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
  smt2_assert(t, tstack_elem_is_special(f));
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
 * [check-sat-assuming <literal>* ]
 */
static void check_smt2_check_sat_assuming(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_CHECK_SAT_ASSUMING);
}

static void eval_smt2_check_sat_assuming(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  signed_symbol_t *buffer;
  uint32_t i;

  buffer = get_sbuffer(stack, n);
  for (i=0; i<n; i++) {
    get_signed_symbol(stack, f+i, buffer+i);
  }
  smt2_check_sat_assuming(n, buffer);
  tstack_pop_frame(stack);
  no_result(stack);
}


static void check_constant_term(tstack_t *stack, stack_elem_t *e) {
  term_t t = get_term(stack, e);
  term_constructor_t kind = yices_term_constructor(t);
  switch (kind) {
  case YICES_BOOL_CONSTANT:
  case YICES_ARITH_CONSTANT:
  case YICES_ARITH_FF_CONSTANT:
  case YICES_BV_CONSTANT:
    break;
  default:
    raise_exception(stack, e, TSTACK_NOT_A_CONSTANT);
  }
}

static void check_all_constants_terms(tstack_t *stack, stack_elem_t *e, stack_elem_t *end) {
  while (e < end) {
    check_constant_term(stack, e);
    e ++;
  }
}

static void check_variable(tstack_t *stack, stack_elem_t *e) {
  term_t t = get_term(stack, e);
  term_constructor_t kind = yices_term_constructor(t);
  switch (kind) {
  case YICES_UNINTERPRETED_TERM:
    break;
  default:
    raise_exception(stack, e, TSTACK_NOT_A_VARIABLE);
  }
}

static void check_all_variables(tstack_t *stack, stack_elem_t *e, stack_elem_t *end) {
  while (e < end) {
    check_variable(stack, e);
    e ++;
  }
}

/*
 * [check-sat-assuming (<symbol>*) (<const term>*) ]
 */
static void check_smt2_check_sat_assuming_model(tstack_t *stack, stack_elem_t *f, uint32_t m) {
  uint32_t n;

  if (m % 2) {
    raise_exception(stack, f, TSTACK_VARIABLES_VALUES_NOT_MATCHING);
  }
  n = m / 2;
  check_all_variables(stack, f, f + n);
  check_all_constants_terms(stack, f + n, f + m);
}

static void eval_smt2_check_sat_assuming_model(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  uint32_t i, m;
  term_t* vars_and_values;

  vars_and_values = (term_t*) safe_malloc(n * sizeof(term_t));

  for (i = 0; i < n; ++ i) {
    vars_and_values[i] = get_term(stack, f + i);
  }

  m = n / 2;
  smt2_check_sat_assuming_model(m, vars_and_values, vars_and_values + m);

  tstack_pop_frame(stack);
  no_result(stack);

  safe_free(vars_and_values);
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
  smt2_declare_sort(f[0].val.string, i);
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
  check_all_tags(stack, f + 1, f + (n-1), TAG_TYPE_BINDING);
  check_distinct_type_binding_names(stack, f+1, n-2);
  check_tag(stack, f + (n-1), TAG_TYPE);
}

static void eval_smt2_define_sort(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  type_t *a;
  uint32_t i, nvars;

  nvars = n - 2;
  a = get_aux_buffer(stack, nvars);
  for (i=0; i<nvars; i++) {
    a[i] = f[i+1].val.type_binding.type;
  }

  smt2_define_sort(f[0].val.string, nvars, a, f[n-1].val.type);

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
  for (i=0; i<ntypes; i++) {
    a[i] = f[i+1].val.type;
  }

  smt2_declare_fun(f[0].val.string, ntypes, a);
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

  smt2_define_fun(f[0].val.string, nvars, a, body, f[n-2].val.type);
  tstack_pop_frame(stack);
  no_result(stack);
}


/*
 * [get-model]
 */
static void check_smt2_get_model(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_GET_MODEL);
  check_size(stack, n == 0);
}

static void eval_smt2_get_model(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_get_model();
  tstack_pop_frame(stack);
  no_result(stack);
}

/*
 * [echo <string>]
 */
static void check_smt2_echo(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_ECHO);
  check_size(stack, n == 1);
  check_tag(stack, f, TAG_STRING);
}

static void eval_smt2_echo(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  smt2_echo(f->val.string);
  tstack_pop_frame(stack);
  no_result(stack);
}

/*
 * [reset-assertions]
 */
static void check_smt2_reset_assertions(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_RESET_ASSERTIONS);
  check_size(stack, n == 0);
}

static void eval_smt2_reset_assertions(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  tstack_reset(stack);
  tstack_reset_buffers(stack);
  smt2_reset_assertions();
  //  tstack_pop_frame(stack);
  //  no_result(stack);
}

/*
 * [reset-all]
 */
static void check_smt2_reset_all(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_RESET_ALL);
  check_size(stack, n == 0);
}

// side effect: this resets the stack and free buffers
static void eval_smt2_reset_all(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  tstack_reset(stack);
  tstack_reset_buffers(stack);
  smt2_reset_all();
  //  tstack_pop_frame(stack);
  //  no_result(stack);
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
 * - the attributes we care about are of the form
 *    :named <symbol>
 *    :pattern <term> ... <term>
 * - for future extensions, we also allow
 *    :keyword <optional-value> where <optional value> is not a keyword
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

/*
 * check whether attribute :named s can be attached to term t
 * raise an exception if t is not ground or if s is already used
 */
static void check_named_attribute(tstack_t *stack, stack_elem_t *f, term_t t, const char *s) {
  if (! yices_term_is_ground(t)) {
    raise_exception(stack, f, SMT2_NAMED_TERM_NOT_GROUND);
  }
  if (yices_get_term_by_name(s) != NULL_TERM) {
    raise_exception(stack, f, SMT2_NAMED_SYMBOL_REUSED);
  }
}

// check whether f[i] is in the frame and is a term
// return the term if so, raise an exception otherwise
static term_t check_pattern(tstack_t *stack, stack_elem_t *f, uint32_t i, uint32_t n) {
  if (i == n) {
    raise_exception(stack, f, SMT2_MISSING_PATTERN);
  }
  return get_term(stack, f+i);
}

static void eval_smt2_add_attributes(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t t, pattern;
  term_t *plist;      // list of terms
  uint32_t np;        // number of terms in the list
  uint32_t i;
  int32_t op;         // enclosing operator
  bool named;         // true if one of the attributes is :named xxx

  t = get_term(stack, f);
  op = get_enclosing_op(stack);
  named = false;

  i = 1;
  while (i<n) {
    switch (get_keyword(stack, f+i)) {
    case SMT2_KW_NAMED:
      // expecting :named <symbol>
      i ++;
      check_name(stack, f, i, n);
      check_named_attribute(stack, f, t, f[i].val.string);
      smt2_add_name(op, t, f[i].val.string);
      named = true;
      i ++;
      break;

    case SMT2_KW_PATTERN:
      // expecting :pattern <term> .... <term>
      // (a non-empty list of terms)
      i ++;
      plist = get_aux_buffer(stack, n); // just make sure there's enough room
      np = 0;
      do {
	pattern = check_pattern(stack, f, i, n);
	plist[np] = pattern;
	np ++;
	i ++;
      } while (i < n && !is_keyword(f + i));
      smt2_add_pattern(op, t, plist, np);
      break;

    default:
      // ignore the attribute and skip the attribute value if there's one
      i ++;
      if (i < n && !is_keyword(f + i)) {
	i ++;
      }
      break;
    }
  }

  tstack_pop_frame(stack);

  // if the term is named and the enclosing op is assert
  // we mark t for special processing
  if (named && op == SMT2_ASSERT) {
    set_special_term_result(stack, t);
  } else {
    set_term_result(stack, t);
  }
}



/*
 * PROCESS SYMBOLS
 */

/*
 * All functions below are variants of push_symbol
 * - s = string, n = its length, loc = location in the input
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
  SMT2_KEY_IDX_FF,       // for ff<numeral> construct
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
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVREDOR (should not occur)
  SMT2_KEY_TERM_OP,      // SMT2_SYM_BVREDAND (should not occur)
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
  SMT2_KEY_IDX_FF,       // SMT2_SYM_FF_CONSTANT
  SMT2_KEY_IDX_TYPE,     // SMT2_SYM_FINITEFIELD
  SMT2_KEY_TERM_OP,      // SMT2_SYM_FFADD
  SMT2_KEY_TERM_OP,      // SMT2_SYM_FFMUL
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
  SMT2_MK_DIV,           // SMT2_SYM_DIV (integer division)
  SMT2_MK_MOD,           // SMT2_SYM_MOD
  SMT2_MK_ABS,           // SMT2_SYM_ABS
  SMT2_MK_TO_REAL,       // SMT2_SYM_TO_REAL (NO_OP for that one)
  SMT2_MK_TO_INT,        // SMT2_SYM_TO_INT
  SMT2_MK_IS_INT,        // SMT2_SYM_IS_INT
  SMT2_MK_DIVISIBLE,     // SMT2_SYM_DIVISIBLE
  MK_BV_CONST,           // SMT2_SYM_BV_CONSTANT (for _bv<value> size)
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
  MK_FF_CONST,           // SMT2_SYM_FF_CONSTANT
  MK_FF_TYPE,            // SMT2_SYM_FINITEFIELD
  MK_FF_ADD,             // SMT2_SYM_FFADD
  MK_FF_MUL,             // SMT2_SYM_FFMUL
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

  case SMT2_KEY_TYPE_OP:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_SORT);
    break;

  default:
    /*
     * The standard allows predefined symbols to be used as sort names
     * provided there's no ambiguity. This is a terrible idea, but
     * we allow anything here.
     */
    tstack_push_type_by_name(stack, s, loc);
    break;
  }
}


/*
 * Name in (define-sort <name> ..) or (declare-sort <name> ...)
 */
void tstack_push_free_sort_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
    /*
     * The standard allows predefined symbols to be used anywhere
     * provided there's no ambiguity. This is a terrible idea.
     *
     * To support this, we must allow anything here that's not
     * a predefined sort or sort constructor.
     */
  case SMT2_KEY_TYPE:
  case SMT2_KEY_TYPE_OP:
    push_exception(stack, loc, s, TSTACK_TYPENAME_REDEF);
    break;

  default:
    tstack_push_free_type_or_macro_name(stack, s, n, loc);
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
 * Symbol as a sort constructor
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
    tstack_push_op(stack, MK_APP_TYPE, loc);
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

  case SMT2_KEY_IDX_FF:
    // generates (_ ffN -1)
    tstack_push_op(stack, MK_FF_CONST, loc);
    tstack_push_rational(stack, s + 2, loc);
    tstack_eval(stack);
    break;

  case SMT2_KEY_TERM_OP:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_TERM);
    break;

  default:
    /*
     * The standard allows predefined symbols to be used as term names
     * provided there's no ambiguity. This is a terrible idea, but
     * we allow anything here.
     */
    tstack_push_term_by_name(stack, s, loc);
    break;
  }
}


/*
 * Name in a function declaration/definition:
 *  (define-fun <name>  ...)
 *  (declare-fun <name> ...)
 */
void tstack_push_free_fun_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
    /*
     * The standard allows predefined symbols to be used anywhere
     * provided there's no ambiguity. This is a terrible idea.
     *
     * To support this, we must allow anything here that's not
     * a predefined term or function here.
     */
  case SMT2_KEY_TERM:
  case SMT2_KEY_TERM_OP:
    push_exception(stack, loc, s, TSTACK_TERMNAME_REDEF);
    break;

  default:
    tstack_push_free_termname(stack, s, n, loc);
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

  case SMT2_KEY_TERM:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_FUNCTION);
    break;

  case SMT2_KEY_UNKNOWN:
  default:
    /*
     * Anything else should? be treated as an uninterpreted function
     */
    tstack_push_op(stack, MK_APPLY, loc);
    tstack_push_term_by_name(stack, s, loc);
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

  case SMT2_KEY_IDX_FF:
    // s is ff<numeral> and it is to be interpreted as (mk-ff <numeral> ...)
    assert(n > 2);
    tstack_push_op(stack, MK_FF_CONST, loc);
    tstack_push_rational(stack, s + 2, loc); // skip the 'ff' prefix
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
 * Symbol in qualified expression
 *  (as <symbol> <sort> )
 */
void tstack_push_qual_term_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  tstack_push_term_name(stack, s, n, loc);
}


/*
 * Indexed symbol in qualified expression:
 *  (as (_ <symbol> <idx> ... <idx>) <sort> )
 */
void tstack_push_qual_idx_term_name(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
    smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
  case SMT2_KEY_IDX_TERM:
    tstack_push_opcode(stack, smt2_val[symbol], loc);
    break;

  case SMT2_KEY_IDX_BV:
    // s is bv<numeral> and is to be interpreted as (mk-bv <numeral> ...)
    assert(n > 2);
    tstack_push_opcode(stack, MK_BV_CONST, loc);
    tstack_push_rational(stack, s + 2, loc); // skip the 'bv' prefix
    break;

  case SMT2_KEY_IDX_FF:
    // s is ff<numeral> and is to be interpreted as (mk-ff <numeral> ...)
    assert(n > 2);
    tstack_push_opcode(stack, MK_FF_CONST, loc);
    tstack_push_rational(stack, s + 2, loc); // skip the 'ff' prefix
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
 * Function name in SORTED_APPLY
 *  ((as <symbol> <sort>) <arg> ... <arg>)
 */
void tstack_push_qual_smt2_op(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
  case SMT2_KEY_TERM_OP:
    tstack_push_opcode(stack, smt2_val[symbol], loc);
    break;

  case SMT2_KEY_UNKNOWN:
    // uninterpreted function
    tstack_push_opcode(stack, MK_APPLY, loc);
    tstack_push_term_by_name(stack, s, loc);
    break;

  default:
    push_exception(stack, loc, s, SMT2_SYMBOL_NOT_FUNCTION);
    break;
  }
}


/*
 * function name in SORTED_INDEXED_APPLY
 *  ((as (_ <symbol> <idx> ... <idx>) <sort>) <arg> ... <arg>)
 */
void tstack_push_qual_smt2_idx_op(tstack_t *stack, char *s, uint32_t n, loc_t *loc) {
  smt2_symbol_t symbol;
  smt2_key_t key;

  symbol = smt2_string_to_symbol(s, n);
  key = smt2_key[symbol];
  switch (key) {
  case SMT2_KEY_IDX_TERM_OP:
    tstack_push_opcode(stack, smt2_val[symbol], loc);
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
 * PLACE-HOLDERS FOR UNSUPPORTED FUNCTIONS
 */
#if 0
static void check_not_supported(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_OP_NOT_IMPLEMENTED);
}

static void eval_not_supported(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}
#endif


/*
 * ARRAY-THEORY
 */

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
 * INDEXED CONSTRUCTORS
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
 * [indexed-apply <symbol> <numeral> ... <numeral> ]
 */
static void check_smt2_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}

static void eval_smt2_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  raise_exception(stack, f, TSTACK_INTERNAL_ERROR);
}




/*
 * SORTED CONSTRUCTORS
 */

/*
 * SMT2 includes constructs similar to type coercion:
 *
 *  (as <symbol> <sort>)
 *  (as (_ <symbol> <numeral> ... <numeral>) <sort>)
 *  ((as <symbol> <sort>) <term> ... <term>)
 *  ((as (_ <symbol> <numeral> ... <numeral>) <sort>) <term> ... <term>)
 *
 * This is intended to disambiguate <symbol> is overloaded.  There's
 * no real need for this given the theories we have, but nothing stops
 * people from using these constructs anyway.  In such cases, we
 * construct the term then check whether it has the correct <sort>.
 */

/*
 * Check whether element e on the stack has type tau
 */
static bool stack_elem_has_type(tstack_t *stack, stack_elem_t *e, type_t tau) {
  uint32_t n;

  switch (e->tag) {
  case TAG_BV64:
    n = e->val.bv64.bitsize;
    break;

  case TAG_BV:
    n = e->val.bv.bitsize;
    break;

  case TAG_RATIONAL:
    return is_real_type(tau) || (is_integer_type(tau) && q_is_integer(&e->val.rational));

  case TAG_FINITEFIELD:
    return is_ff_type(__yices_globals.types, tau) && q_eq(&e->val.ff.mod, ff_type_size(__yices_globals.types, tau));

  case TAG_TERM:
  case TAG_SPECIAL_TERM:
    return yices_check_term_type(e->val.term, tau);

  case TAG_ARITH_BUFFER:
    return is_real_type(tau) ||
      (is_integer_type(tau) && yices_arith_buffer_is_int(e->val.arith_buffer));

  case TAG_ARITH_FF_BUFFER:
    return is_ff_type(__yices_globals.types, tau)
    && q_eq(&e->val.mod_arith_buffer.mod, ff_type_size(__yices_globals.types, tau));

  case TAG_BVARITH64_BUFFER:
    n = bvarith64_buffer_bitsize(e->val.bvarith64_buffer);
    break;

  case TAG_BVARITH_BUFFER:
    n = bvarith_buffer_bitsize(e->val.bvarith_buffer);
    break;

  case TAG_BVLOGIC_BUFFER:
    n = bvlogic_buffer_bitsize(e->val.bvlogic_buffer);
    break;

  default:
    raise_exception(stack, e, TSTACK_INTERNAL_ERROR);
    break;
  }

  /*
   * e is a bitvector of n bits
   * - we use the fact that yices_bvtype_size(tau) returns 0
   *   if tau is not (bitvector k).
   */
  assert(n > 0);
  return yices_bvtype_size(tau) == n;
}

/*
 * Check whether the element has a type compatible with tau
 * - if not, raise exception TYPE_ERROR_IN_QUAL
 */
static void check_elem_type(tstack_t *stack, stack_elem_t *e, type_t tau) {
  if (!stack_elem_has_type(stack, e, tau)) {
    raise_exception(stack, e, SMT2_TYPE_ERROR_IN_QUAL);
  }
}

static inline void check_topelem_type(tstack_t *stack, type_t tau) {
  assert(stack->top > 0);
  check_elem_type(stack, stack->elem + (stack->top - 1), tau);
}

/*
 * Finalizes a stack element once the type is known.
 * Used for (as <elem> <type>) expressions.
 */
static void stack_elem_finalize_type(tstack_t *stack, stack_elem_t *e, type_t tau) {
  switch (e->tag) {
  case TAG_FINITEFIELD:
    if (q_is_minus_one(&e->val.ff.mod) && is_ff_type(__yices_globals.types, tau)) {
      q_set(&e->val.ff.mod, ff_type_size(__yices_globals.types, tau));
    }
    break;

  default:
    break;
  }
}


/*
 * Scan the stack starting from f to f+n, and return the index of the
 * first element that has tag 'TYPE'. Return n if there's no such
 * element.
 */
static uint32_t find_type_elem(stack_elem_t *f, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (f[i].tag == TAG_TYPE) break;
  }

  return i;
}


/*
 * Shift stack elements:
 * - copy f[0 ... n-1] into f[1 ... n]
 *   f[0] is left unchanged, f[n] is lost
 */
static void shift_stack_elems(stack_elem_t *f, uint32_t n) {
  while (n > 0) {
    f[n] = f[n-1];
    n --;
  }
}



/*
 * [sorted-term <xxx> <type>]
 *
 * The first argument is always a term (cf. push_qual_term_name). But this may
 * change so we use get_term.
 */
static void check_smt2_sorted_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_SORTED_TERM);
  check_size(stack, n == 2);
  check_tag(stack, f+1, TAG_TYPE);
}

static void eval_smt2_sorted_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  term_t t;
  type_t tau;

  tau = f[1].val.type;

  // finalize the type before making it a term
  stack_elem_finalize_type(stack, f, tau);

  t = get_term(stack, f);

  tstack_pop_frame(stack);
  set_term_result(stack, t);

  check_topelem_type(stack, tau);
}


/*
 * [sorted-indexed-term <opcode> <numeral> ... <numeral> <type>]
 *
 * This is for (as (_ <symbol> <numeral> ... <numeral>) <sort>)
 */
static void check_smt2_sorted_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_SORTED_INDEXED_TERM);
  check_size(stack, n >= 3);
  check_tag(stack, f, TAG_OPCODE);
  check_all_tags(stack, f + 1, f + (n-1), TAG_RATIONAL);
  check_tag(stack, f + (n-1), TAG_TYPE);
}

static void eval_smt2_sorted_indexed_term(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t op;
  type_t tau;

  tau = f[n-1].val.type;
  op = f[0].val.op;
  call_tstack_check(stack, op, f+1, n-2);
  call_tstack_eval(stack, op, f+1, n-2);

  check_topelem_type(stack, tau);
}


/*
 * [sorted-apply <symbol> <type> <term> .... <term> ]
 *
 * For SMT2 expression ((as <symbol> <sort>) <arg> ... <arg>)
 */
static void check_smt2_sorted_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_SORTED_APPLY);
  check_size(stack, n >= 3);
  check_tag(stack, f, TAG_OPCODE);
  check_tag(stack, f+1, TAG_TYPE);
}

static void eval_smt2_sorted_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t op;
  type_t tau;

  /*
   * frame content:
   *   f[0] = opcode
   *   f[1] = sort
   *   f[2 ... n-1] = arguments
   */
  op = f[0].val.op;
  tau = f[1].val.type;

  call_tstack_check(stack, op, f+2, n-2);
  call_tstack_eval(stack, op, f+2, n-2);

  check_topelem_type(stack, tau);
}


/*
 * [sorted-indexed-apply <symbol> <numeral> ... <numeral> <type> <term> ... <term>]
 *
 * For SMT2 expression ((as (_ <symbol> <idx> ... <idx>) <sort>) <arg> ... <arg>)
 */
static void check_smt2_sorted_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, SMT2_SORTED_INDEXED_APPLY);
  check_size(stack, n >= 4);
  check_tag(stack, f, TAG_OPCODE);
}

static void eval_smt2_sorted_indexed_apply(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t op;
  type_t tau;
  uint32_t k;

  /*
   * frame content:
   *   f[0] = opcode
   *   f[1 ... k-1] = indices
   *   f[k] = sort
   *   f[k+1 ... n-1] = arguments
   */
  op  = f[0].val.op;
  k = find_type_elem(f, n);
  assert(2 <= k && k < n && f[k].tag == TAG_TYPE);
  tau = f[k].val.type;

  // shift f[1 ... k-1] into f[2 ... k]
  shift_stack_elems(f+1, k-1);

  call_tstack_check(stack, op, f+2, n-2);
  call_tstack_eval(stack, op, f+2, n-2);

  check_topelem_type(stack, tau);
}




/*
 * Initialize stack for smt2:
 * - must be called after init_smt2
 */
void init_smt2_tstack(tstack_t *stack) {
  init_tstack(stack, NUM_SMT2_OPCODES);
  tstack_set_avtbl(stack, __smt2_globals.avtbl);

  // overwrites the default OPs (from term_stack2.c) for SMT2, in case they are different
  tstack_add_op(stack, MK_BV_CONST, false, eval_smt2_mk_bv_const, check_smt2_mk_bv_const);
  tstack_add_op(stack, MK_BV_ROTATE_LEFT, false, eval_smt2_mk_bv_rotate_left, check_smt2_mk_bv_rotate_left);
  tstack_add_op(stack, MK_BV_ROTATE_RIGHT, false, eval_smt2_mk_bv_rotate_right, check_smt2_mk_bv_rotate_right);
  tstack_add_op(stack, MK_BV_REPEAT, false, eval_smt2_mk_bv_repeat, check_smt2_mk_bv_repeat);
  tstack_add_op(stack, MK_BV_SIGN_EXTEND, false, eval_smt2_mk_bv_sign_extend, check_smt2_mk_bv_sign_extend);
  tstack_add_op(stack, MK_BV_ZERO_EXTEND, false, eval_smt2_mk_bv_zero_extend, check_smt2_mk_bv_zero_extend);
  tstack_add_op(stack, MK_IMPLIES, false, eval_smt2_mk_implies, check_smt2_mk_implies);
  tstack_add_op(stack, MK_EQ, false, eval_smt2_mk_eq, check_smt2_mk_eq);
  tstack_add_op(stack, MK_GE, false, eval_smt2_mk_ge, check_smt2_mk_ge);
  tstack_add_op(stack, MK_GT, false, eval_smt2_mk_gt, check_smt2_mk_gt);
  tstack_add_op(stack, MK_LE, false, eval_smt2_mk_le, check_smt2_mk_le);
  tstack_add_op(stack, MK_LT, false, eval_smt2_mk_lt, check_smt2_mk_lt);
  tstack_add_op(stack, MK_BV_NAND, false, eval_smt2_mk_bv_nand, check_smt2_mk_bv_nand);
  tstack_add_op(stack, MK_BV_NOR, false, eval_smt2_mk_bv_nor, check_smt2_mk_bv_nor);
  tstack_add_op(stack, MK_BV_XNOR, false, eval_smt2_mk_bv_xnor, check_smt2_mk_bv_xnor);

  tstack_add_op(stack, SMT2_EXIT, false, eval_smt2_exit, check_smt2_exit);
  tstack_add_op(stack, SMT2_SILENT_EXIT, false, eval_smt2_silent_exit, check_smt2_silent_exit);
  tstack_add_op(stack, SMT2_GET_ASSERTIONS, false, eval_smt2_get_assertions, check_smt2_get_assertions);
  tstack_add_op(stack, SMT2_GET_ASSIGNMENT, false, eval_smt2_get_assignment, check_smt2_get_assignment);
  tstack_add_op(stack, SMT2_GET_PROOF, false, eval_smt2_get_proof, check_smt2_get_proof);
  tstack_add_op(stack, SMT2_GET_UNSAT_CORE, false, eval_smt2_get_unsat_core, check_smt2_get_unsat_core);
  tstack_add_op(stack, SMT2_GET_UNSAT_ASSUMPTIONS, false, eval_smt2_get_unsat_assumptions, check_smt2_get_unsat_assumptions);
  tstack_add_op(stack, SMT2_GET_UNSAT_MODEL_INTERPOLANT, false, eval_smt2_get_unsat_model_interpolant, check_smt2_get_unsat_model_interpolant);
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
  tstack_add_op(stack, SMT2_CHECK_SAT_ASSUMING, false, eval_smt2_check_sat_assuming, check_smt2_check_sat_assuming);
  tstack_add_op(stack, SMT2_CHECK_SAT_ASSUMING_MODEL, false, eval_smt2_check_sat_assuming_model, check_smt2_check_sat_assuming_model);
  tstack_add_op(stack, SMT2_DECLARE_SORT, false, eval_smt2_declare_sort, check_smt2_declare_sort);
  tstack_add_op(stack, SMT2_DEFINE_SORT, false, eval_smt2_define_sort, check_smt2_define_sort);
  tstack_add_op(stack, SMT2_DECLARE_FUN, false, eval_smt2_declare_fun, check_smt2_declare_fun);
  tstack_add_op(stack, SMT2_DEFINE_FUN, false, eval_smt2_define_fun, check_smt2_define_fun);

  tstack_add_op(stack, SMT2_GET_MODEL, false, eval_smt2_get_model, check_smt2_get_model);
  tstack_add_op(stack, SMT2_ECHO, false, eval_smt2_echo, check_smt2_echo);
  tstack_add_op(stack, SMT2_RESET_ASSERTIONS, false, eval_smt2_reset_assertions, check_smt2_reset_assertions);
  tstack_add_op(stack, SMT2_RESET_ALL, false, eval_smt2_reset_all, check_smt2_reset_all);

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

  tstack_add_op(stack, SMT2_MK_TO_REAL, false, eval_smt2_to_real, check_smt2_to_real);
  tstack_add_op(stack, SMT2_MK_DIV, false, eval_smt2_div, check_smt2_div);
  tstack_add_op(stack, SMT2_MK_MOD, false, eval_smt2_mod, check_smt2_mod);
  tstack_add_op(stack, SMT2_MK_ABS, false, eval_smt2_abs, check_smt2_abs);
  tstack_add_op(stack, SMT2_MK_TO_INT, false, eval_smt2_to_int, check_smt2_to_int);
  tstack_add_op(stack, SMT2_MK_IS_INT, false, eval_smt2_is_int, check_smt2_is_int);
  tstack_add_op(stack, SMT2_MK_DIVISIBLE, false, eval_smt2_divisible, check_smt2_divisible);
  tstack_add_op(stack, MK_DIVISION, false, eval_smt2_mk_division, check_smt2_mk_division);
}
