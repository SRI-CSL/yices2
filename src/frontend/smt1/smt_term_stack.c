/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TERM-STACK OPERATIONS FOR SMT-LIB 1.2
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <stdint.h>
#include <assert.h>

#include "yices.h"
#include "api/yices_extensions.h"
#include "terms/tstack_internals.h"
#include "frontend/smt1/smt_term_stack.h"


/*
 * Raise exception on Yices error
 */
static void check_term(tstack_t *stack, term_t t) {
  if (t == NULL_TERM) report_yices_error(stack);
}

/*
 * SMT variant for [mk-eq <term> ... <term>]
 * we rewrite (eq t1 ... tn) to (and (eq t1 tn) ... (eq t_{n-1} t_n))
 */
static void smt_check_mk_eq(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_EQ);
  check_size(stack, n >= 2);
}

static void smt_eval_mk_eq(tstack_t *stack, stack_elem_t *f, uint32_t n) {
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
 * [mk-bv-const <value> <size>]
 * - arguments are swapped. The Yices version is (mk-bvconst <size> <value>)
 */
static void smt_check_mk_bv_const(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_CONST);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_RATIONAL);
  check_tag(stack, f+1, TAG_RATIONAL);
}

static void smt_eval_mk_bv_const(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t size;
  rational_t *val;

  size = get_integer(stack, f+1);
  val = &f[0].val.rational;
  mk_bv_const_core(stack, f, size, val);
}



/*
 * [mk-bv-rotate-left <rational> <bv>]
 * arguments are swapped: Yices uses (rotate <bv> <rational>)
 */
static void smt_check_mk_bv_rotate_left(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_ROTATE_LEFT);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_RATIONAL);
}

static void smt_eval_mk_bv_rotate_left(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t index;
  bvlogic_buffer_t *b;

  index = get_integer(stack, f);
  b = tstack_get_bvlbuffer(stack);
  bvl_set_elem(stack, b, f+1);
  if (! yices_check_bitshift(b, index)) {
    report_yices_error(stack);
  }
  // we known 0 <= index <= bitsize of b
  if (index < bvlogic_buffer_bitsize(b)) {
    bvlogic_buffer_rotate_left(b, index);
  }
  tstack_pop_frame(stack);
  set_bvlogic_result(stack, b);
}


/*
 * Rotate-right: same issue
 */
static void smt_check_mk_bv_rotate_right(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_ROTATE_RIGHT);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_RATIONAL);
}

static void smt_eval_mk_bv_rotate_right(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  int32_t index;
  bvlogic_buffer_t *b;

  index = get_integer(stack, f);
  b = tstack_get_bvlbuffer(stack);
  bvl_set_elem(stack, b, f+1);
  if (! yices_check_bitshift(b, index)) {
    report_yices_error(stack);
  }
  // we known 0 <= index <= bitsize of b
  if (index < bvlogic_buffer_bitsize(b)) {
    bvlogic_buffer_rotate_right(b, index);
  }
  tstack_pop_frame(stack);
  set_bvlogic_result(stack, b);
}


/*
 * [mk-bv-repeat <rational> <bv>]
 */
static void smt_check_mk_bv_repeat(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_REPEAT);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_RATIONAL);
}

static void smt_eval_mk_bv_repeat(tstack_t *stack, stack_elem_t *f, uint32_t n) {
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
 * [mk-bv-sign-extend <rational> <bv>]
 */
static void smt_check_mk_bv_sign_extend(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_SIGN_EXTEND);
  check_size(stack, n == 2);
  check_size(stack, f[0].tag == TAG_RATIONAL);
}

static void smt_eval_mk_bv_sign_extend(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  if (f[0].tag == TAG_RATIONAL) {
    mk_bv_sign_extend_core(stack, f+1, f);
  } else {
    assert(f[1].tag == TAG_RATIONAL);
    mk_bv_sign_extend_core(stack, f, f+1);
  }
}


/*
 * SMT-LIB variant [mk-bv-zero-extend <rational> <bv>]
 * rational n = number of bits to add
 */
static void smt_check_mk_bv_zero_extend(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  check_op(stack, MK_BV_ZERO_EXTEND);
  check_size(stack, n == 2);
  check_tag(stack, f, TAG_RATIONAL);
}

static void smt_eval_mk_bv_zero_extend(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  mk_bv_zero_extend_core(stack, f+1, f);
}



/*
 * Initialize stack then install all these operations
 */
void init_smt_tstack(tstack_t *stack) {
  init_tstack(stack, NUM_BASE_OPCODES);
  tstack_add_op(stack, MK_EQ, false, smt_eval_mk_eq, smt_check_mk_eq);
  tstack_add_op(stack, MK_BV_CONST, false, smt_eval_mk_bv_const, smt_check_mk_bv_const);
  tstack_add_op(stack, MK_BV_ROTATE_LEFT, false, smt_eval_mk_bv_rotate_left, smt_check_mk_bv_rotate_left);
  tstack_add_op(stack, MK_BV_ROTATE_RIGHT, false, smt_eval_mk_bv_rotate_right, smt_check_mk_bv_rotate_right);
  tstack_add_op(stack, MK_BV_REPEAT, false, smt_eval_mk_bv_repeat, smt_check_mk_bv_repeat);
  tstack_add_op(stack, MK_BV_SIGN_EXTEND, false, smt_eval_mk_bv_sign_extend, smt_check_mk_bv_sign_extend);
  tstack_add_op(stack, MK_BV_ZERO_EXTEND, false, smt_eval_mk_bv_zero_extend, smt_check_mk_bv_zero_extend);
}
