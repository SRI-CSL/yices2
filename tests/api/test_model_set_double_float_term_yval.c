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
  type_t bool_type = yices_bool_type();
  term_t var1 = yices_new_uninterpreted_term(int_type);
  term_t var2 = yices_new_uninterpreted_term(int_type);
  term_t var3 = yices_new_uninterpreted_term(bool_type);
  model_t *model = yices_new_model();
  yval_t yval;
  yval_t bad_tag_yval;
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

  // Error: bad yval tag
  bad_tag_yval = yval;
  bad_tag_yval.node_tag = YVAL_BOOL;
  if (yices_model_set_yval(model, var3, &bad_tag_yval) >= 0) {
    fprintf(stderr, "Expected error for setting yval with wrong tag, but call succeeded\n");
    exit(1);
  } else {
    yices_print_error(stderr);
  }

  // Error: type mismatch (integer yval assigned to boolean var)
  if (yices_model_set_yval(model, var3, &yval) >= 0) {
    fprintf(stderr, "Expected error for type mismatch in set_yval, but call succeeded\n");
    exit(1);
  } else {
    yices_print_error(stderr);
  }

  yices_free_model(model);
}

static void test_tuple_model_setting(void) {
  type_t int_type = yices_int_type();
  type_t bool_type = yices_bool_type();
  type_t tuple_type = yices_tuple_type2(int_type, bool_type);
  term_t int_var = yices_new_uninterpreted_term(int_type);
  term_t bool_var = yices_new_uninterpreted_term(bool_type);
  term_t tuple_var = yices_new_uninterpreted_term(tuple_type);
  model_t *model = yices_new_model();
  yval_t int_yval;
  yval_t bool_yval;
  yval_t tuple_yval;
  yval_t elem[2];
  yval_t child[2];
  yval_t bad_tag;
  int32_t ival;
  int32_t bval;
  int32_t code;

  if (yices_model_set_int32(model, int_var, 10) != 0 ||
      yices_model_set_bool(model, bool_var, 1) != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  if (yices_get_value(model, int_var, &int_yval) != 0 ||
      yices_get_value(model, bool_var, &bool_yval) != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  elem[0] = int_yval;
  elem[1] = bool_yval;

  // Build tuple value from yvals
  if (yices_model_make_tuple(model, 2, elem, &tuple_yval) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  assert(tuple_yval.node_tag == YVAL_TUPLE);

  // Assign tuple value via dedicated API
  if (yices_model_set_tuple(model, tuple_var, 2, elem) != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  if (yices_get_value(model, tuple_var, &tuple_yval) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  if (yices_val_expand_tuple(model, &tuple_yval, child) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  if (yices_val_get_int32(model, &child[0], &ival) != 0 ||
      yices_val_get_bool(model, &child[1], &bval) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  assert(ival == 10);
  assert(bval == 1);

  // Error: bad descriptor tag in tuple builder
  bad_tag = int_yval;
  bad_tag.node_tag = YVAL_BOOL;
  elem[0] = bad_tag;
  code = yices_model_make_tuple(model, 2, elem, &tuple_yval);
  if (code >= 0) {
    fprintf(stderr, "Expected error for invalid yval tag in tuple builder, but call succeeded\n");
    exit(1);
  } else {
    yices_print_error(stderr);
  }

  yices_free_model(model);
}

static void test_function_model_setting(void) {
  type_t int_type = yices_int_type();
  type_t bool_type = yices_bool_type();
  type_t fun_type = yices_function_type1(int_type, bool_type);
  term_t int_var0 = yices_new_uninterpreted_term(int_type);
  term_t int_var1 = yices_new_uninterpreted_term(int_type);
  term_t bool_var_true = yices_new_uninterpreted_term(bool_type);
  term_t bool_var_false = yices_new_uninterpreted_term(bool_type);
  term_t fun_var = yices_new_uninterpreted_term(fun_type);
  model_t *model = yices_new_model();
  yval_t arg0;
  yval_t arg1;
  yval_t val_true;
  yval_t val_false;
  yval_t def;
  yval_t map0;
  yval_t map1;
  yval_t maps[2];
  yval_t args[1];
  yval_t bad_map;
  yval_t fun;
  term_t app0, app1, app2;
  int32_t b;

  if (yices_model_set_int32(model, int_var0, 0) != 0 ||
      yices_model_set_int32(model, int_var1, 1) != 0 ||
      yices_model_set_bool(model, bool_var_true, 1) != 0 ||
      yices_model_set_bool(model, bool_var_false, 0) != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  if (yices_get_value(model, int_var0, &arg0) != 0 ||
      yices_get_value(model, int_var1, &arg1) != 0 ||
      yices_get_value(model, bool_var_true, &val_true) != 0 ||
      yices_get_value(model, bool_var_false, &val_false) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  def = val_false;

  args[0] = arg0;
  if (yices_model_make_mapping(model, 1, args, &val_true, &map0) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  args[0] = arg1;
  if (yices_model_make_mapping(model, 1, args, &val_false, &map1) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  assert(map0.node_tag == YVAL_MAPPING);
  assert(map1.node_tag == YVAL_MAPPING);

  maps[0] = map0;
  maps[1] = map1;

  if (yices_model_make_function(model, fun_type, 2, maps, &def, &fun) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  assert(fun.node_tag == YVAL_FUNCTION);

  if (yices_model_set_function(model, fun_var, 2, maps, &def) != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  app0 = yices_application1(fun_var, yices_int32(0));
  app1 = yices_application1(fun_var, yices_int32(1));
  app2 = yices_application1(fun_var, yices_int32(2));
  if (yices_get_bool_value(model, app0, &b) != 0 || b != 1) {
    yices_print_error(stderr);
    exit(1);
  }
  if (yices_get_bool_value(model, app1, &b) != 0 || b != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  if (yices_get_bool_value(model, app2, &b) != 0 || b != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  // Error: invalid mapping descriptor
  bad_map = map0;
  bad_map.node_tag = YVAL_BOOL;
  maps[0] = bad_map;
  if (yices_model_make_function(model, fun_type, 2, maps, &def, &fun) >= 0) {
    fprintf(stderr, "Expected error for invalid mapping descriptor, but call succeeded\n");
    exit(1);
  } else {
    yices_print_error(stderr);
  }

  yices_free_model(model);
}

#if HAVE_MCSAT
static void test_algebraic_leaf_tuple_and_function_values(void) {
  ctx_config_t *cfg;
  context_t *ctx;
  model_t *model;
  term_t x, minus_x, eq, tuple_var, fun_var;
  type_t tuple_type, fun_type;
  yval_t x_yval, minus_x_yval, tuple_yval, fun_yval;
  yval_t tuple_elem[2];
  yval_t tuple_child[2];
  yval_t int0_yval, map_yval, def_yval, maps[1], map_args[1];
  int32_t code;
  smt_status_t status;
  double d0, d1, d2;

  // Build a model where x is algebraic: x^2 = 2
  cfg = yices_new_config();
  assert(cfg != NULL);
  code = yices_default_config_for_logic(cfg, "QF_NRA");
  assert(code == 0);
  ctx = yices_new_context(cfg);
  assert(ctx != NULL);
  yices_free_config(cfg);

  x = yices_new_uninterpreted_term(yices_real_type());
  minus_x = yices_neg(x);
  eq = yices_parse_term("(= (* x x) 2)");
  assert(x != NULL_TERM && minus_x != NULL_TERM && eq != NULL_TERM);
  code = yices_assert_formula(ctx, eq);
  if (code != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  status = yices_check_context(ctx, NULL);
  if (status != YICES_STATUS_SAT) {
    fprintf(stderr, "Expected SAT status in algebraic example\n");
    exit(1);
  }
  model = yices_get_model(ctx, true);
  assert(model != NULL);

  code = yices_get_value(model, x, &x_yval);
  assert(code == 0 && x_yval.node_tag == YVAL_ALGEBRAIC);
  code = yices_get_value(model, minus_x, &minus_x_yval);
  assert(code == 0 && minus_x_yval.node_tag == YVAL_ALGEBRAIC);

  // Tuple with algebraic leaves
  tuple_type = yices_tuple_type2(yices_real_type(), yices_real_type());
  tuple_var = yices_new_uninterpreted_term(tuple_type);
  tuple_elem[0] = x_yval;
  tuple_elem[1] = minus_x_yval;

  code = yices_model_make_tuple(model, 2, tuple_elem, &tuple_yval);
  assert(code == 0 && tuple_yval.node_tag == YVAL_TUPLE);
  code = yices_model_set_tuple(model, tuple_var, 2, tuple_elem);
  assert(code == 0);
  code = yices_get_value(model, tuple_var, &tuple_yval);
  assert(code == 0 && tuple_yval.node_tag == YVAL_TUPLE);
  code = yices_val_expand_tuple(model, &tuple_yval, tuple_child);
  assert(code == 0);
  assert(tuple_child[0].node_tag == YVAL_ALGEBRAIC);
  assert(tuple_child[1].node_tag == YVAL_ALGEBRAIC);

  code = yices_val_get_double(model, &tuple_child[0], &d0);
  assert(code == 0);
  code = yices_val_get_double(model, &tuple_child[1], &d1);
  assert(code == 0);
  // Second tuple component should be the negation of the first.
  assert(d0 * d1 < 0.0);

  // Function Int -> Real with algebraic leaves
  fun_type = yices_function_type1(yices_int_type(), yices_real_type());
  fun_var = yices_new_uninterpreted_term(fun_type);

  code = yices_get_value(model, yices_int32(0), &int0_yval);
  assert(code == 0);
  map_args[0] = int0_yval;
  code = yices_model_make_mapping(model, 1, map_args, &minus_x_yval, &map_yval);
  assert(code == 0 && map_yval.node_tag == YVAL_MAPPING);

  maps[0] = map_yval;
  def_yval = x_yval;
  code = yices_model_make_function(model, fun_type, 1, maps, &def_yval, &fun_yval);
  assert(code == 0 && fun_yval.node_tag == YVAL_FUNCTION);
  code = yices_model_set_function(model, fun_var, 1, maps, &def_yval);
  assert(code == 0);

  // f(0) = -x from mapping
  code = yices_get_double_value(model, yices_application1(fun_var, yices_int32(0)), &d2);
  assert(code == 0);
  assert(d2 * d1 > 0.0);

  // f(1) = x from default
  code = yices_get_double_value(model, yices_application1(fun_var, yices_int32(1)), &d2);
  assert(code == 0);
  assert(d2 * d0 > 0.0);

  yices_free_model(model);
  yices_free_context(ctx);
}
#endif

int main(void) {
  yices_init();

  test_double_float_model_setting();
  test_term_model_setting();
  test_yval_model_setting();
  test_tuple_model_setting();
  test_function_model_setting();
#if HAVE_MCSAT
  if (yices_has_mcsat()) {
    test_algebraic_leaf_tuple_and_function_values();
  }
#endif

  printf("All tests passed!\n");

  yices_exit();
  return 0;
} 
