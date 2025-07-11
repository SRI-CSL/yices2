/*
 * Test yices_model_set_double, yices_model_set_float, yices_model_set_term, yices_model_set_yval
 */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <yices.h>

static void test_double_float_model_setting(void) {
  type_t real_type = yices_real_type();
  term_t var = yices_new_uninterpreted_term(real_type);
  model_t *model = yices_new_model();
  double dval;

  // Set double value
  if (yices_model_set_double(model, var, 3.14) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  if (yices_get_double_value(model, var, &dval) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  assert(dval == 3.14);

  // Set float value (should fail, already assigned)
  if (yices_model_set_float(model, var, 2.71f) >= 0) {
    fprintf(stderr, "Expected error for setting float value on already assigned variable, but call succeeded\n");
    exit(1);
  } else {
    yices_print_error(stderr);
  }

  yices_free_model(model);

  // Set float value on new variable
  var = yices_new_uninterpreted_term(real_type);
  model = yices_new_model();
  if (yices_model_set_float(model, var, 2.71f) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  if (yices_get_double_value(model, var, &dval) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  assert((float)dval == 2.71f);
  yices_free_model(model);
}

static void test_term_model_setting(void) {
  type_t int_type = yices_int_type();
  term_t var = yices_new_uninterpreted_term(int_type);
  model_t *model = yices_new_model();
  term_t value = yices_int32(42);
  term_t out;

  // Set term value
  if (yices_model_set_term(model, var, value) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  out = yices_get_value_as_term(model, var);
  if (out != value) {
    exit(1);
  }

  // Error: set again
  if (yices_model_set_term(model, var, value) >= 0) {
    fprintf(stderr, "Expected error for setting term value again, but call succeeded\n");
    exit(1);
  } else {
    yices_print_error(stderr);
  }

  // Error: type mismatch - set real value to int variable
  if (yices_model_set_term(model, var, yices_parse_rational("3.14")) >= 0) {
    fprintf(stderr, "Expected error for type mismatch in set_term, but call succeeded\n");
    exit(1);
  } else {
    yices_print_error(stderr);
  }

  yices_free_model(model);
}

static void test_yval_model_setting(void) {
  type_t int_type = yices_int_type();
  term_t var1 = yices_new_uninterpreted_term(int_type);
  term_t var2 = yices_new_uninterpreted_term(int_type);
  model_t *model = yices_new_model();
  yval_t yval;
  int32_t ival;

  // Set var1 in model
  if (yices_model_set_int32(model, var1, 123) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  // Get yval from model
  if (yices_get_value(model, var1, &yval) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  // Set var2 in same model using yval
  if (yices_model_set_yval(model, var2, &yval) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  // Check value
  if (yices_get_int32_value(model, var2, &ival) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  assert(ival == 123);

  // Error: set again
  if (yices_model_set_yval(model, var2, &yval) >= 0) {
    fprintf(stderr, "Expected error for setting yval again, but call succeeded\n");
    exit(1);
  } else {
    yices_print_error(stderr);
  }

  yices_free_model(model);
}

int main(void) {
  yices_init();

  test_double_float_model_setting();
  test_term_model_setting();
  test_yval_model_setting();

  printf("All tests passed!\n");

  yices_exit();
  return 0;
} 
