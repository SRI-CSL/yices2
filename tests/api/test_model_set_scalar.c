/*
 * Test yices_model_set_scalar function
 */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "assert.h"

#include <yices.h>

/*
 * Test setting scalar values in a model
 */
static void test_scalar_model_setting(void) {
  type_t scalar_type;
  term_t var0, var1, var2;
  model_t *model;
  int32_t val;

  // Create a scalar type with 3 elements
  scalar_type = yices_new_scalar_type(3);
  assert(scalar_type != NULL_TYPE);

  // Create uninterpreted terms of scalar type
  var0 = yices_new_uninterpreted_term(scalar_type);
  var1 = yices_new_uninterpreted_term(scalar_type);
  var2 = yices_new_uninterpreted_term(scalar_type);
  assert(var0 != NULL_TERM);
  assert(var1 != NULL_TERM);
  assert(var2 != NULL_TERM);

  // Create a new model
  model = yices_new_model();
  assert(model != NULL);

  // Test setting scalar value 0
  assert(yices_model_set_scalar(model, var0, 0) == 0);

  // Verify the value was set correctly
  assert(yices_get_scalar_value(model, var0, &val) == 0);
  assert(val == 0);

  // Test setting scalar value 1
  assert(yices_model_set_scalar(model, var1, 1) == 0);

  // Verify the value was set correctly
  assert(yices_get_scalar_value(model, var1, &val) == 0);
  assert(val == 1);

  // Test setting scalar value 2
  assert(yices_model_set_scalar(model, var2, 2) == 0);

  // Verify the value was set correctly
  assert(yices_get_scalar_value(model, var2, &val) == 0);
  assert(val == 2);

  // Test setting invalid scalar value (should fail)
  assert(yices_model_set_scalar(model, var0, 3) < 0); // Should fail for value >= cardinality

  yices_free_model(model);
}

/*
 * Test setting uninterpreted type values in a model
 */
static void test_uninterpreted_model_setting(void) {
  type_t uninterpreted_type;
  term_t var0, var1, var2;
  model_t *model;
  int32_t val;

  // Create an uninterpreted type
  uninterpreted_type = yices_new_uninterpreted_type();
  assert(uninterpreted_type != NULL_TYPE);

  // Create uninterpreted terms
  var0 = yices_new_uninterpreted_term(uninterpreted_type);
  var1 = yices_new_uninterpreted_term(uninterpreted_type);
  var2 = yices_new_uninterpreted_term(uninterpreted_type);
  assert(var0 != NULL_TERM);
  assert(var1 != NULL_TERM);
  assert(var2 != NULL_TERM);

  // Create a new model
  model = yices_new_model();
  assert(model != NULL);

  // Test setting various values
  assert(yices_model_set_scalar(model, var0, 0) == 0);

  assert(yices_get_scalar_value(model, var0, &val) == 0);
  assert(val == 0);

  assert(yices_model_set_scalar(model, var1, 42) == 0);

  assert(yices_get_scalar_value(model, var1, &val) == 0);
  assert(val == 42);

  assert(yices_model_set_scalar(model, var2, 1000) == 0);

  assert(yices_get_scalar_value(model, var2, &val) == 0);
  assert(val == 1000);

  yices_free_model(model);
}

/*
 * Test error conditions
 */
static void test_error_conditions(void) {
  type_t int_type, scalar_type;
  term_t int_var, scalar_var;
  model_t *model;

  int_type = yices_int_type();
  scalar_type = yices_new_scalar_type(2);
  int_var = yices_new_uninterpreted_term(int_type);
  scalar_var = yices_new_uninterpreted_term(scalar_type);

  model = yices_new_model();

  // Test setting scalar value on non-scalar term (should fail)
  assert(yices_model_set_scalar(model, int_var, 0) < 0);

  // Test setting invalid scalar value
  assert(yices_model_set_scalar(model, scalar_var, -1) < 0);

  assert(yices_model_set_scalar(model, scalar_var, 2) < 0);

  yices_free_model(model);
}

int main(void) {
  yices_init();

  test_scalar_model_setting();
  test_uninterpreted_model_setting();
  test_error_conditions();

  printf("All tests passed!\n");

  yices_exit();
  return 0;
} 
