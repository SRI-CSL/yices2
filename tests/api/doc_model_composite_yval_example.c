/*
 * Compile/run checked version of the model-operations composite yval example.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <yices.h>

int main(void) {
  model_t *model;
  type_t int_type, bool_type, tuple_type, fun_type;
  term_t x, y, b, t, f, fxy, fyx;
  yval_t xv, yv, bv, tuple_v, map_v, false_v, fun_v;
  yval_t tuple_elems[3], map_args[2], maps[1];
  yval_t tuple_children[3];
  int32_t bval, ival;

  yices_init();

  model = yices_new_model();
  assert(model != NULL);

  int_type = yices_int_type();
  bool_type = yices_bool_type();
  tuple_type = yices_tuple_type3(int_type, int_type, bool_type);
  fun_type = yices_function_type2(int_type, int_type, bool_type);

  x = yices_new_uninterpreted_term(int_type);
  y = yices_new_uninterpreted_term(int_type);
  b = yices_new_uninterpreted_term(bool_type);
  t = yices_new_uninterpreted_term(tuple_type);
  f = yices_new_uninterpreted_term(fun_type);

  if (yices_model_set_int32(model, x, 3) != 0 ||
      yices_model_set_int32(model, y, 5) != 0 ||
      yices_model_set_bool(model, b, 1) != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  if (yices_get_value(model, x, &xv) != 0 ||
      yices_get_value(model, y, &yv) != 0 ||
      yices_get_value(model, b, &bv) != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  // Tuple: (x, y, b)
  tuple_elems[0] = xv;
  tuple_elems[1] = yv;
  tuple_elems[2] = bv;
  if (yices_model_make_tuple(model, 3, tuple_elems, &tuple_v) != 0 ||
      yices_model_set_tuple(model, t, 3, tuple_elems) != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  if (yices_get_value(model, t, &tuple_v) != 0 ||
      yices_val_expand_tuple(model, &tuple_v, tuple_children) != 0 ||
      yices_val_get_int32(model, &tuple_children[0], &ival) != 0 ||
      ival != 3) {
    yices_print_error(stderr);
    exit(1);
  }

  // Mapping: [x, y -> b]
  map_args[0] = xv;
  map_args[1] = yv;
  if (yices_model_make_mapping(model, 2, map_args, &bv, &map_v) != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  // Function with one mapping and default false
  if (yices_get_value(model, yices_false(), &false_v) != 0) {
    yices_print_error(stderr);
    exit(1);
  }
  maps[0] = map_v;
  if (yices_model_make_function(model, fun_type, 1, maps, &false_v, &fun_v) != 0 ||
      yices_model_set_function(model, f, 1, maps, &false_v) != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  // f(x, y) = true from mapping
  fxy = yices_application2(f, x, y);
  if (yices_get_bool_value(model, fxy, &bval) != 0 || bval != 1) {
    yices_print_error(stderr);
    exit(1);
  }

  // f(y, x) = false from default
  fyx = yices_application2(f, y, x);
  if (yices_get_bool_value(model, fyx, &bval) != 0 || bval != 0) {
    yices_print_error(stderr);
    exit(1);
  }

  yices_free_model(model);
  yices_exit();
  printf("All tests passed!\n");

  return 0;
}
