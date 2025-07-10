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
  assert(yices_model_set_double(model, var, 3.14) == 0);
  assert(yices_get_double_value(model, var, &dval) == 0);
  assert(dval == 3.14);

  // Set float value (should fail, already assigned)
  assert(yices_model_set_float(model, var, 2.71f) < 0);

  yices_free_model(model);

  // Set float value on new variable
  var = yices_new_uninterpreted_term(real_type);
  model = yices_new_model();
  assert(yices_model_set_float(model, var, 2.71f) == 0);
  assert(yices_get_double_value(model, var, &dval) == 0);
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
  assert(yices_model_set_term(model, var, value) == 0);
  out = yices_get_value_as_term(model, var);
  assert(out == value);

  // Error: set again
  assert(yices_model_set_term(model, var, value) < 0);

  // Error: type mismatch - set real value to int variable
  assert(yices_model_set_term(model, var, yices_parse_rational("3.14")) < 0);

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
  assert(yices_model_set_int32(model, var1, 123) == 0);
  // Get yval from model
  assert(yices_get_value(model, var1, &yval) == 0);
  // Set var2 in same model using yval
  assert(yices_model_set_yval(model, var2, &yval) == 0);
  // Check value
  assert(yices_get_int32_value(model, var2, &ival) == 0);
  assert(ival == 123);

  // Error: set again
  assert(yices_model_set_yval(model, var2, &yval) < 0);

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
