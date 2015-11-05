/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of stack-based term construction
 */

#include <stdint.h>
#include <inttypes.h>
#include <setjmp.h>
#include <stdio.h>

#include "api/yices_globals.h"
#include "io/term_printer.h"
#include "io/type_printer.h"
#include "parser_utils/term_stack2.h"
#include "yices.h"


static char *code2string[NUM_TSTACK_ERRORS] = {
  "no error",
  "internal error",
  "operation not supported",
  "undefined term",
  "undefined type",
  "invalid rational format",
  "invalid float format",
  "invalid bitvector binary format",
  "invalid bitvector hexadecimal format",
  "type name already used",
  "term name already used",
  "invalid operation",
  "incorrect frame format",
  "constant too large",
  "constant is not an integer",
  "symbol required",
  "numeric constant required",
  "type required",
  "error in arithmetic operation",
  "division by zero",
  "denominator is not a constant",
  "bitsize must be positive",
  "number cannot be converted to a bitvector",
  "error in bitvector arithmetic operation",
  "error in bitvector operation",
  "yices error",
};

static tstack_t stack;
static loc_t loc;

int main(void) {
  int exception;
  type_t tau;
  term_t t;

  yices_init();
  init_tstack(&stack, NUM_BASE_OPCODES);
  loc.line = 0;
  loc.column = 0;

  exception = setjmp(stack.env);
  if (exception == 0) {
    // fake location
    loc.line ++;
    loc.column = 0;
    printf("test: (define-type bool <bool-type>)\n");
    fflush(stdout);
    loc.column ++;
    tstack_push_op(&stack, DEFINE_TYPE, &loc);
    loc.column ++;
    tstack_push_free_typename(&stack, "bool", 4, &loc);
    loc.column ++;
    tstack_push_bool_type(&stack, &loc);
    tstack_eval(&stack);

    if (! tstack_is_empty(&stack)) {
      printf("*** Error: stack not empty ***\n");
    }

    tau = yices_get_type_by_name("bool");
    if (tau == NULL_TYPE) {
      printf("*** bool not defined as a type ***\n");
    } else {
      printf("*** bool --> ");
      print_type_def(stdout, __yices_globals.types, tau);
      printf("\n");
      printf("*** yices_get_type_by_name(bool) = %"PRId32"\n", tau);
      printf("*** yices_bool_type() = %"PRId32"\n", yices_bool_type());
    }


    loc.line ++;
    loc.column = 0;
    printf("\ntest: (define-type bv5 (bitvector 5))\n");
    fflush(stdout);

    loc.column ++;
    tstack_push_op(&stack, DEFINE_TYPE, &loc);
    loc.column ++;
    tstack_push_free_typename(&stack, "bv5", 3, &loc);
    loc.column ++;
    tstack_push_op(&stack, MK_BV_TYPE, &loc);
    loc.column ++;
    tstack_push_rational(&stack, "5", &loc);
    tstack_eval(&stack);
    tstack_eval(&stack);

    if (! tstack_is_empty(&stack)) {
      printf("*** Error: stack not empty ***\n");
    }

    tau = yices_get_type_by_name("bv5");
    if (tau == NULL_TYPE) {
      printf("*** BUG: bv5 not defined as a type ***\n");
    } else {
      printf("*** bv5 --> ");
      print_type_def(stdout, __yices_globals.types, tau);
      printf("\n");
      printf("*** yices_get_type_by_name(bv5) = %"PRId32"\n", tau);
      printf("*** yices_bv_type(5) = %"PRId32"\n", yices_bv_type(5));
    }


    loc.line ++;
    loc.column = 0;
    printf("\ntest: (define xxx::int (let (x 1) (let (y 2) (+ x y))))\n");
    fflush(stdout);

    loc.column ++;
    tstack_push_op(&stack, DEFINE_TERM, &loc);
    loc.column ++;
    tstack_push_free_termname(&stack, "xxx", 3, &loc);
    loc.column ++;
    tstack_push_int_type(&stack, &loc);
    loc.column ++;
    tstack_push_op(&stack, LET, &loc);
    loc.column ++;
    tstack_push_op(&stack, BIND, &loc);
    loc.column ++;
    tstack_push_string(&stack, "x", 1, &loc);
    loc.column ++;
    tstack_push_rational(&stack, "1", &loc);
    tstack_eval(&stack);
    loc.column ++;
    tstack_push_op(&stack, LET, &loc);
    loc.column ++;
    tstack_push_op(&stack, BIND, &loc);
    loc.column ++;
    tstack_push_string(&stack, "y", 1, &loc);
    loc.column ++;
    tstack_push_rational(&stack, "2", &loc);
    tstack_eval(&stack);
    loc.column ++;
    tstack_push_op(&stack, MK_ADD, &loc);
    loc.column ++;
    tstack_push_term_by_name(&stack, "x", &loc);
    loc.column ++;
    tstack_push_term_by_name(&stack, "y", &loc);
    tstack_eval(&stack);
    tstack_eval(&stack);
    tstack_eval(&stack);
    tstack_eval(&stack);

    if (! tstack_is_empty(&stack)) {
      printf("*** Error: stack not empty ***\n");
    }

    t = yices_get_term_by_name("xxx");
    if (t== NULL_TERM) {
      printf("*** BUG: xxx not defined as a term ***\n");
    } else {
      printf("*** xxx --> ");
      print_term_def(stdout, __yices_globals.terms, t);
      printf("\n");
    }

    loc.line ++;
    loc.column = 0;
    printf("\ntest: (define yyy::int (let (x 1) (let (x 2) (+ x x))))\n");
    fflush(stdout);

    loc.column ++;
    tstack_push_op(&stack, DEFINE_TERM, &loc);
    loc.column ++;
    tstack_push_free_termname(&stack, "yyy", 3, &loc);
    loc.column ++;
    tstack_push_int_type(&stack, &loc);
    loc.column ++;
    tstack_push_op(&stack, LET, &loc);
    loc.column ++;
    tstack_push_op(&stack, BIND, &loc);
    loc.column ++;
    tstack_push_string(&stack, "x", 1, &loc);
    loc.column ++;
    tstack_push_rational(&stack, "1", &loc);
    tstack_eval(&stack);
    loc.column ++;
    tstack_push_op(&stack, LET, &loc);
    loc.column ++;
    tstack_push_op(&stack, BIND, &loc);
    loc.column ++;
    tstack_push_string(&stack, "x", 1, &loc);
    loc.column ++;
    tstack_push_rational(&stack, "2", &loc);
    tstack_eval(&stack);
    loc.column ++;
    tstack_push_op(&stack, MK_ADD, &loc);
    loc.column ++;
    tstack_push_term_by_name(&stack, "x", &loc);
    loc.column ++;
    tstack_push_term_by_name(&stack, "x", &loc);
    tstack_eval(&stack);
    tstack_eval(&stack);
    tstack_eval(&stack);
    tstack_eval(&stack);

    if (! tstack_is_empty(&stack)) {
      printf("*** Error: stack not empty ***\n");
    }

    t = yices_get_term_by_name("yyy");
    if (t== NULL_TERM) {
      printf("*** BUG: yyy not defined as a term ***\n");
    } else {
      printf("*** yyy --> ");
      print_term_def(stdout, __yices_globals.terms, t);
      printf("\n");
    }

  } else {
    printf("Exception: %s\n", code2string[exception]);
    if (stack.error_string != NULL) {
      printf("---> string = %s\n", stack.error_string);
    }
    printf("---> code = %d\n", exception);
    printf("---> line = %"PRId32"\n", stack.error_loc.line);
    printf("---> column = %"PRId32"\n", stack.error_loc.column);
    printf("---> op = %d\n", stack.error_op);
    tstack_reset(&stack);
  }

  printf("\n");
  delete_tstack(&stack);
  yices_exit();
  return 0;
}
