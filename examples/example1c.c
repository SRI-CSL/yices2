/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
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
 * Same as examples/example1.c except that we use print functions
 * that take file descriptor as arguments rather than FILE*
 */

#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>

#include "yices.h"


/*
 * How to call the pretty printer (via a file descriptor)
 * - this also shows how to check for errors
 *   and print an error message if something goes wrong
 */
static void print_term(term_t term) {
  int32_t code;

  code = yices_pp_term_fd(1, term, 80, 20, 0); // print to stdout (fd = 1)
  if (code < 0) {
    // An error occurred
    fprintf(stderr, "Error in print_term: ");
    yices_print_error_fd(2);  // print to stderr (fd = 2)
    exit(1);
  }
}


/*
 * Small example: equivalent to
 *
 *  (define x::int)
 *  (define y::int)
 *  (assert (and (>= x 0) (>= y 0)(= (+ x y) 100)))
 *  (check)
 *
 * Then we query the model to get the values of x and y.
 */
static void simple_test(void) {
  int32_t code;

  /*
   * Build the formula
   */
  // Create two uninterpreted terms of type int.
  type_t int_type = yices_int_type();
  term_t x = yices_new_uninterpreted_term(int_type);
  term_t y = yices_new_uninterpreted_term(int_type);

  // Assign names "x" and "y" to these terms.
  // This is optional, but we need the names in yices_parse_term
  // and it makes pretty printing nicer.
  yices_set_term_name(x, "x");
  yices_set_term_name(y, "y");

  // Build the formula (and (>= x 0) (>= y 0) (= (+ x y) 100))
  term_t f = yices_and3(yices_arith_geq0_atom(x), // x >= 0
			yices_arith_geq0_atom(y), // y >= 0
			yices_arith_eq_atom(yices_add(x, y), yices_int32(100))); // x + y = 100


  // Another way to do it
  term_t f_var = yices_parse_term("(and (>= x 0) (>= y 0) (= (+ x y) 100))");


  /*
   * Print the formulas: f and f_var should be identical
   */
  printf("Formula f\n");
  print_term(f);
  printf("Formula f_var\n");
  print_term(f_var);


  /*
   * To check whether f is satisfiable
   * - first build a context
   * - assert f in the context
   * - call check_context
   * - if check_context returns SAT, build a model
   *   and make queries about the model.
   */
  context_t *ctx = yices_new_context(NULL);  // NULL means 'use default configuration'
  code = yices_assert_formula(ctx, f);
  if (code < 0) {
    fprintf(stderr, "Assert failed: code = %"PRId32", error = %"PRId32"\n", code, yices_error_code());
    yices_print_error_fd(2);    
  }

  switch (yices_check_context(ctx, NULL)) { // call check_context, NULL means 'use default heuristics'
  case STATUS_SAT:
    printf("The formula is satisfiable\n");
    model_t* model = yices_get_model(ctx, true);  // get the model
    if (model == NULL) {
      fprintf(stderr, "Error in get_model\n");
      yices_print_error_fd(2);
    } else {
      printf("Model\n");
      code = yices_pp_model_fd(1, model, 80, 4, 0); // print the model to stodut

      int32_t v;
      code = yices_get_int32_value(model, x, &v);   // get the value of x, we know it fits int32
      if (code < 0) {
	fprintf(stderr, "Error in get_int32_value for 'x'\n");
	yices_print_error_fd(2); // stderr
      } else {
	printf("Value of x = %"PRId32"\n", v);
      }

      code = yices_get_int32_value(model, y, &v);   // get the value of y
      if (code < 0) {
	fprintf(stderr, "Error in get_int32_value for 'y'\n");
	yices_print_error_fd(2);
      } else {
	printf("Value of y = %"PRId32"\n", v);
      }

      yices_free_model(model); // clean up: delete the model
    }
    break;
      
  case STATUS_UNSAT:
    printf("The formula is not satisfiable\n");
    break;

  case STATUS_UNKNOWN:
    printf("The status is unknown\n");
    break;

  case STATUS_IDLE:
  case STATUS_SEARCHING:
  case YICES_STATUS_INTERRUPTED:
  case STATUS_ERROR:
    fprintf(stderr, "Error in check_context\n");
    yices_print_error_fd(2);
    break;
  }

  yices_free_context(ctx);   // delete the context
}


int main(void) {
  yices_init();    // Always call this first
  simple_test();
  yices_exit();    // Cleanup 

  return 0;
}
