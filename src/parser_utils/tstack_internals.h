/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * INTERNAL/LOW-LEVEL TERM-STACK OPERATIONS
 */

/*
 * Low-level functions that manipulate internal tstack structures
 * are declared here and implemented in term_stack.c.
 *
 * They should be used only for defining new term stack operations or
 * modifying existing term stack operations.
 *
 * To add or change an operation, define two functions
 * - void check_some_op(tstack_t *stack, stack_elem_t *e, uint32_t n)
 * - void eval_some_op((tstack_t *stack, stack_elem_t *e, uint32_t n)
 *
 * then install both in stack using
 *   tstack_add_op(stack, opcode, flag, eval_new_op, check_new_op);
 *
 * - opcode should be an integer constant (cf. term_stack.h)
 * - flag should be true for associative operations, false otherwise.
 */


#ifndef __TSTACK_INTERNALS_H
#define __TSTACK_INTERNALS_H

#include "parser_utils/term_stack2.h"


/*
 * Raise an exception when processing element e
 * - stack->error_pos is set to e->pos
 * - stack->error_op is set to stack->top_op
 * - stack->error_string is set to e's string field if e is a symbol or a binding,
 *   or to NULL otherwise.
 * code is returned to the enclosing exception handler by longjmp
 *
 * NOTE: It's possible to raise exceptions that are not defined in tstack_error_t
 * by using an integer code > TSTACK_YICES_ERROR. This requires that the interrupt
 * handler knows how to deal with such codes.
 */
extern void __attribute__((noreturn)) raise_exception(tstack_t *stack, stack_elem_t *e, int code);


/*
 * Raise an exception when pushing data on the stack
 * - stack->error_pos is set to loc
 * - stack->error_string is set to s (not a copy)
 * then code is returned to the enclosing exception handler by longjmp
 */
extern void __attribute__((noreturn)) push_exception(tstack_t *stack, loc_t *loc, char *s, int code);


/*
 * Raise an exception when a yices function returns NULL_TERM or another error code.
 * - this raises exception TSTACK_YICES_ERROR
 * - stack->error_loc is set to the top-frame's location
 * - stack->error_op is set to the top_operator code
 * - stack->error_string is NULL
 */
extern void __attribute__((noreturn)) report_yices_error(tstack_t *stack);


/*
 * Check whether e->tag is equal to tg
 * - if not raise an exception
 */
extern void check_tag(tstack_t *stack, stack_elem_t *e, tag_t tg);


/*
 * Check whether cond is true (cond should be a constraint on the number of elements
 * on the top frame). If cond is false, raise exception INVALID_FRAME.
 */
extern void check_size(tstack_t *stack, bool cond);


/*
 * Check whether the top operator is equal to op.
 * - if not raise exception INTERNAL_ERROR
 */
extern void check_op(tstack_t *stack, int32_t op);


/*
 * Check whether all elements from e to end have tag tg
 * - if not raise an exception
 *
 * This is equivalent to
 *   for (t = e; t<end; t++) {
 *     check_tag(stack, t, tg);
 *   }
 */
extern void check_all_tags(tstack_t *stack, stack_elem_t *e, stack_elem_t *end, tag_t tg);


/*
 * Check whether all names in a list of variable bindings are distinct
 * - names are in f[0] .. f[n-1]
 * - all must be  bindings (tag == TAG_BINDING)
 * if the test fails, raise exception DUPLICATE_VAR_NAME
 */
extern void check_distinct_binding_names(tstack_t *stack, stack_elem_t *f, uint32_t n);


/*
 * Check whether all names in a list of type variables are distinct
 * - names are in f[0] .. f[n-1]
 * - all must be have tag == TAG_TYPE_BINDING
 * if the test fails, raise exception DUPLICATE_TYPE_VAR_NAME
 */
extern void check_distinct_type_binding_names(tstack_t *stack, stack_elem_t *f, uint32_t n);



/*
 * OPERATORS
 */

/*
 * To implement term annotations/attributes, we need to know the context
 * (i.e., the enclosing operator of an annotated term).
 *
 * For example: (assert (! <term> :named xxx)) must be treated as
 * a named assertion rather than the assertion of a named term.
 * To deal with this, we allow term-stack functions to query the term stack
 * to examine the current top and the enclosing operator:
 * - get_top_op returns the top-level operator (or NO_OP if the stack is empty)
 * - get_enclosing_op returns the previous operator on the stack (or NO_OP
 *   if there's just one frame on the stack).
 *
 * Examples:
 * 1) in (assert (! <term> :named xxx)), the stack will
 *    have two operators: [ASSERT [ADD_ATTRIBUTES <term> ...]].
 *    When we process ADD_ATTRIBUTES:
 *      top_op = ADD_ATTRIBUTES
 *      enclosing_op = ASSERT
 *
 * 2) in (forall ((x T)) (! (P X) :pattern xxx))
 *    The stack will have [FORALL [BINDING ..] [ADD_ATTRIBUTES <term> ...]
 *    When we process ADD_ATTRIBUTES:
 *      top_op = ADD_ATTRIBUTES
 *      enclosing_op = FORALL
 */
static inline int32_t get_top_op(tstack_t *stack) {
  return stack->top_op; // equal to NO_OP if the stack is empty
}

extern int32_t get_enclosing_op(tstack_t *stack);



/*
 * CONVERSION
 */

/*
 * Convert element e to a term or raise an exception if e can't be converted
 */
extern term_t get_term(tstack_t *stack, stack_elem_t *e);


/*
 * Return the integer value of e (e must have rational tag)
 * Raise an exception if e is too large or is not an integer.
 */
extern int32_t get_integer(tstack_t *stack, stack_elem_t *e);


/*
 * Support for division: return a rational constant equal to den
 * provided den is constant and non-zero
 *
 * Raise exception otherwise
 */
extern rational_t *get_divisor(tstack_t *stack, stack_elem_t *den);


/*
 * BUFFER ALLOCATION
 */

/*
 * All operations below return an initialized/empty buffer that can be
 * pushed onto the stack using set_arith_result,
 * set_bvarith64_results, and variants.
 */
extern rba_buffer_t *tstack_get_abuffer(tstack_t *stack);
extern bvarith64_buffer_t *tstack_get_bva64buffer(tstack_t *stack, uint32_t bitsize);
extern bvarith_buffer_t *tstack_get_bvabuffer(tstack_t *stack, uint32_t bitsize);
extern bvlogic_buffer_t *tstack_get_bvlbuffer(tstack_t *stack);


/*
 * Make the auxiliary buffer large enough for n integers
 */
extern void extend_aux_buffer(tstack_t *stack, uint32_t n);

static inline int32_t *get_aux_buffer(tstack_t *stack, uint32_t n) {
  if (stack->aux_size < n) {
    extend_aux_buffer(stack, n);
  }
  return stack->aux_buffer;
}


/*
 * ARITHMETIC AND BITVECTOR OPERATIONS
 */

/*
 * All operations update a buffer using a stack element e
 * - the functions attempt to convert e to a term or constant of the
 *   right type. then apply the operation to buffer
 */
// arithmetic
extern void add_elem(tstack_t *stack, rba_buffer_t *b, stack_elem_t *e);
extern void sub_elem(tstack_t *stack, rba_buffer_t *b, stack_elem_t *e);
extern void mul_elem(tstack_t *stack, rba_buffer_t *b, stack_elem_t *e);

// bitvector arithmetic for size <= 64
extern void bva64_add_elem(tstack_t *stack, bvarith64_buffer_t *b, stack_elem_t *e);
extern void bva64_sub_elem(tstack_t *stack, bvarith64_buffer_t *b, stack_elem_t *e);
extern void bva64_mul_elem(tstack_t *stack, bvarith64_buffer_t *b, stack_elem_t *e);

// bitvector arithmetic for size > 64
extern void bva_add_elem(tstack_t *stack, bvarith_buffer_t *b, stack_elem_t *e);
extern void bva_sub_elem(tstack_t *stack, bvarith_buffer_t *b, stack_elem_t *e);
extern void bva_mul_elem(tstack_t *stack, bvarith_buffer_t *b, stack_elem_t *e);


// copy e into b
extern  void bvl_set_elem(tstack_t *stack, bvlogic_buffer_t *b, stack_elem_t *e);

// copy e[i..j] into b (must satisfy 0 <= i < j < e's size)
extern void bvl_set_slice_elem(tstack_t *stack, bvlogic_buffer_t *b, uint32_t i, uint32_t j, stack_elem_t *e);

// add e to the right of b (i.e., high-order bits are from b, low-order bits from e)
extern void bvconcat_elem(tstack_t *stack, bvlogic_buffer_t *b, stack_elem_t *e);

// bitwise operations
extern void bvand_elem(tstack_t *stack, bvlogic_buffer_t *b, stack_elem_t *e);
extern void bvor_elem(tstack_t *stack, bvlogic_buffer_t *b, stack_elem_t *e);
extern void bvxor_elem(tstack_t *stack, bvlogic_buffer_t *b, stack_elem_t *e);
extern void bvcomp_elem(tstack_t *stack, bvlogic_buffer_t *b, stack_elem_t *e);


/*
 * In place operations: modify e
 */
// replace e by -e. raise an exception if e is not an arithmetic object
extern void neg_elem(tstack_t *stack, stack_elem_t *e);

// negate e (2's complement): raise an exception if e is not bitvector
extern void bvneg_elem(tstack_t *stack, stack_elem_t *e);


/*
 * Check whether e is a bitvector constant
 */
extern bool elem_is_bvconst(stack_elem_t *e);


/*
 * Copy the constant value of e into c
 * - e must satisfy elem_is_bvconst(e)
 */
extern void bvconst_set_elem(bvconstant_t *c, stack_elem_t *e);



/*
 * POP_FRAME AND STORE RESULTS
 */

/*
 * Remove the top-frame (except the operator)
 * - this must be followed by set_xxx_result, which replaces the top
 *   stack element element by a result
 */
extern void tstack_pop_frame(tstack_t *stack);

/*
 * Replace the top stack element by a new value
 * - this keeps the top-element's loc field unchanged
 */
extern void set_term_result(tstack_t *stack, term_t t);
extern void set_type_result(tstack_t *stack, type_t tau);
extern void set_binding_result(tstack_t *stack, term_t t, char *symbol);
extern void set_type_binding_result(tstack_t *stack, type_t, char *symbol);
extern void set_bv64_result(tstack_t *stack, uint32_t nbits, uint64_t c);
extern void set_bv_result(tstack_t *stack, uint32_t nbits, uint32_t *bv);
extern void set_arith_result(tstack_t *stack, rba_buffer_t *b);
extern void set_bvarith64_result(tstack_t *stack, bvarith64_buffer_t *b);
extern void set_bvarith_result(tstack_t *stack, bvarith_buffer_t *b);
extern void set_bvlogic_result(tstack_t *stack, bvlogic_buffer_t *b);
extern void set_aval_result(tstack_t *stack, aval_t v);

// no result: remove the top element
static inline void no_result(tstack_t *stack) {
  stack->top --;
}

/*
 * Copy v as result in place of the current stack->frame
 * then remove all elements above the top frame index.
 * - v must be a pointer in the current top frame
 * - v's TAG must not be string/symbol.
 */
extern void copy_result_and_pop_frame(tstack_t *stack, stack_elem_t *v);


/*
 * CALL AN EXISTING OPERATION
 */

/*
 * Call the function check[op] or eval[op] on f[0] .... f[n-1]
 * - call_tstack_eval removes the top frame and stores the result of
 *   (op f[0] ... f[n-1]) on top of the stack.
 */
extern void call_tstack_check(tstack_t *stack, int32_t op, stack_elem_t *f, uint32_t n);
extern void call_tstack_eval(tstack_t *stack, int32_t op, stack_elem_t *f, uint32_t n);



/*
 * BIT-VECTOR OPERATIONS
 */

/*
 * The functions below are exported to help support both Yices-2 and SMT-LIB
 * notations. The Yices2 and SMT-LIB versions are identical but take arguments
 * in the opposite order.
 */

/*
 * Build bitvector constant defined by val and size:
 * - size = number of bits
 * - val = value
 * - f = frame index: it's used for error reporting only
 * Raise an exception if size <= 0 or size > MAX_BV_SIZE or val is not a non-negative
 * integer.
 */
extern void mk_bv_const_core(tstack_t *stack, stack_elem_t *f, int32_t size, rational_t *val);


/*
 * Sign-extend and zero-extend:
 * - bv = stack element expected to contain the bitvector
 * - idx = stack element expected to contain an integer
 *
 * These should be used for MK_BV_SIGN_EXTEND and MK_BV_ZERO_EXTEND,
 * which require a stack frame with two arguments. One of them
 * should be bv the other one should be idx.
 *
 * These functions check the arguments bv and idx then push the
 * zero/sign extension bv + idx bits on top of the stack.
 */
extern void mk_bv_sign_extend_core(tstack_t *stack, stack_elem_t *bv, stack_elem_t *idx);
extern void mk_bv_zero_extend_core(tstack_t *stack, stack_elem_t *bv, stack_elem_t *idx);


#endif /* __TSTACK_INTERNALS */
