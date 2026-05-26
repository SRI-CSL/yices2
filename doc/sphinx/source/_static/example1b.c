#include <stdlib.h>
#include <stdio.h>

#include "yices.h"


/*
 * How to call the pretty printer
 * - this also shows how to check for errors
 *   and print an error message if something goes wrong
 */
static void print_term(term_t term) {
  char *s; 

  s = yices_term_to_string(term, 80, 20, 0);
  if (s == NULL) {
    // An error occurred
    s = yices_error_string();
    fprintf(stderr, "Error in print_term: %s\n", s);
    yices_free_string(s);
    exit(1);
  }
  // print the string then free it
  printf("%s\n", s);
  yices_free_string(s);
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
  int code, v;
  term_t x, y, f, f_var;
  type_t int_type;
  context_t *ctx;
  model_t* model;
  char *s;

  /*
   * Build the formula
   */
  // Create two uninterpreted terms of type int.
  int_type = yices_int_type();
  x = yices_new_uninterpreted_term(int_type);
  y = yices_new_uninterpreted_term(int_type);

  // Assign names "x" and "y" to these terms.
  // This is optional, but we need the names in yices_parse_term
  // and it makes pretty printing nicer.
  yices_set_term_name(x, "x");
  yices_set_term_name(y, "y");

  // Build the formula (and (>= x 0) (>= y 0) (= (+ x y) 100))
  f = yices_and3(yices_arith_geq0_atom(x), // x >= 0
			yices_arith_geq0_atom(y), // y >= 0
			yices_arith_eq_atom(yices_add(x, y), yices_int32(100))); // x + y = 100


  // Another way to do it
  f_var = yices_parse_term("(and (>= x 0) (>= y 0) (= (+ x y) 100))");


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
  ctx = yices_new_context(NULL);  // NULL means 'use default configuration'
  code = yices_assert_formula(ctx, f);
  if (code < 0) {
    fprintf(stderr, "Assert failed: code = %d, error = %d\n", code, yices_error_code());
    //    yices_print_error(stderr);
  }

  switch (yices_check_context(ctx, NULL)) { // call check_context, NULL means 'use default heuristics'
  case YICES_STATUS_SAT:
    printf("The formula is satisfiable\n");
    model = yices_get_model(ctx, 1);  // get the model
    if (model == NULL) {
      fprintf(stderr, "Error in get_model\n");
      //      yices_print_error(stderr);
    } else {
      s = yices_model_to_string(model, 80, 4, 0);
      printf("Model\n");
      printf("%s\n", s);
      yices_free_string(s);

      code = yices_get_int32_value(model, x, &v);   // get the value of x, we know it fits int32
      if (code < 0) {
	fprintf(stderr, "Error in get_int32_value for 'x'\n");
	//	yices_print_error(stderr);
      } else {
	printf("Value of x = %d\n", v);
      }

      code = yices_get_int32_value(model, y, &v);   // get the value of y
      if (code < 0) {
	fprintf(stderr, "Error in get_int32_value for 'y'\n");
	//	yices_print_error(stderr);
      } else {
	printf("Value of y = %d\n", v);
      }

      yices_free_model(model); // clean up: delete the model
    }
    break;
      
  case YICES_STATUS_UNSAT:
    printf("The formula is not satisfiable\n");
    break;

  case YICES_STATUS_UNKNOWN:
    printf("The status is unknown\n");
    break;

  case YICES_STATUS_IDLE:
  case YICES_STATUS_SEARCHING:
  case YICES_STATUS_INTERRUPTED:
  case YICES_STATUS_ERROR:
    fprintf(stderr, "Error in check_context\n");
    yices_print_error(stderr);
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
