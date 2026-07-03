/*
 * Tests for model clone/project support and adjacent model-domain behavior.
 */

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>

#include "api/yices_globals.h"
#include "api/yval.h"
#include "model/models.h"
#include "yices.h"

static void check(bool cond, const char *msg) {
  if (!cond) {
    fprintf(stderr, "%s\n", msg);
    yices_print_error(stderr);
    assert(false);
  }
}

static bool vector_has_term(const term_vector_t *v, term_t t) {
  uint32_t i;

  for (i = 0; i < v->size; i++) {
    if (v->data[i] == t) {
      return true;
    }
  }
  return false;
}

static void check_int_yval(model_t *mdl, const yval_t *val, int32_t expected, const char *msg) {
  int32_t actual;

  check(yices_val_get_int32(mdl, val, &actual) == 0, msg);
  check(actual == expected, msg);
}

static void check_bool_yval(model_t *mdl, const yval_t *val, int32_t expected, const char *msg) {
  int32_t actual;

  check(yices_val_get_bool(mdl, val, &actual) == 0, msg);
  check(actual == expected, msg);
}

static void test_collect_defined_terms_named_and_unnamed(void) {
  model_t *mdl;
  term_vector_t v;
  term_t x, y;

  x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "named_collect_x");
  y = yices_new_uninterpreted_term(yices_int_type());

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create model");
  check(yices_model_set_int32(mdl, x, 10) == 0, "failed to set named term");
  check(yices_model_set_int32(mdl, y, 20) == 0, "failed to set unnamed term");

  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(mdl, &v);

  check(v.size == 2, "expected exactly two defined terms");
  check(vector_has_term(&v, x), "missing named defined term");
  check(vector_has_term(&v, y), "missing unnamed defined term");

  yices_delete_term_vector(&v);
  yices_free_model(mdl);
}

static void test_collect_defined_terms_ignores_negative_keys(void) {
  model_t *mdl;
  term_vector_t v;
  term_t b, not_b;

  b = yices_new_uninterpreted_term(yices_bool_type());
  not_b = yices_not(b);

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create model");

  model_map_term(mdl, not_b, vtbl_mk_bool(model_get_vtbl(mdl), true));

  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(mdl, &v);

  check(v.size == 0, "negative model key must not be a defined term");
  check(!vector_has_term(&v, not_b), "negative key was collected");
  check(!vector_has_term(&v, b), "positive term should not be inferred from negative key");

  yices_delete_term_vector(&v);
  yices_free_model(mdl);
}

static void test_collect_defined_terms_alias_domain_only(void) {
  model_t *mdl;
  term_vector_t v;
  term_t x, y, x_plus_one;
  int32_t value;

  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  x_plus_one = yices_add(x, yices_int32(1));
  check(x_plus_one != NULL_TERM, "failed to build x + 1");

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create model");
  model_add_substitution(mdl, y, x_plus_one);

  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(mdl, &v);

  check(v.size == 1, "expected exactly one alias-domain defined term");
  check(vector_has_term(&v, y), "alias-domain term was not collected");
  check(!vector_has_term(&v, x), "default-completed alias RHS dependency was collected");

  check(yices_get_int32_value(mdl, y, &value) == 0, "failed to evaluate alias term");
  check(value == 1, "expected y = default(x) + 1");
  check(yices_get_int32_value(mdl, x, &value) == 0, "failed to evaluate defaulted term");
  check(value == 0, "expected default(x) = 0");

  yices_reset_term_vector(&v);
  yices_model_collect_defined_terms(mdl, &v);
  check(v.size == 1, "evaluation changed the defined-term domain");
  check(vector_has_term(&v, y), "alias-domain term was lost after evaluation");
  check(!vector_has_term(&v, x), "evaluation made default-completed term defined");

  yices_delete_term_vector(&v);
  yices_free_model(mdl);
}

static void test_export_value_source_free_composites(void) {
  model_t *src, *dst;
  type_t int_type, bool_type, bv_type, uninterpreted_type, fun2_type, fun1_type;
  term_t x, y, b, bv_var, scalar_var, g, h, app;
  yval_t xv, yv, bv, false_v, zero_v, one_v, five_v, eleven_v, thirteen_v;
  yval_t tuple_src, tuple_dst, tuple_child[3];
  yval_t tuple_elem[3];
  yval_t map_args[2], fun2_map, fun2_src, fun2_dst;
  yval_t map1_src, fun1_src, update_src, update_dst;
  yval_t bv_src, bv_dst, scalar_src, scalar_dst;
  yval_t int_dst;
  yval_t maps[1];
  value_table_t *src_vtbl;
  value_t update_arg[1], update;
  int32_t bits[4], out_bits[4], bval, ival, scalar_idx;
  type_t scalar_type;

  int_type = yices_int_type();
  bool_type = yices_bool_type();
  bv_type = yices_bv_type(4);
  uninterpreted_type = yices_new_uninterpreted_type();
  fun2_type = yices_function_type2(int_type, int_type, bool_type);
  fun1_type = yices_function_type1(int_type, int_type);

  x = yices_new_uninterpreted_term(int_type);
  y = yices_new_uninterpreted_term(int_type);
  b = yices_new_uninterpreted_term(bool_type);
  bv_var = yices_new_uninterpreted_term(bv_type);
  scalar_var = yices_new_uninterpreted_term(uninterpreted_type);

  src = yices_new_model();
  dst = yices_new_model();
  check(src != NULL && dst != NULL, "failed to create export models");

  bits[0] = 1;
  bits[1] = 0;
  bits[2] = 1;
  bits[3] = 1;
  check(yices_model_set_int32(src, x, 3) == 0, "failed to set x in export source");
  check(yices_model_set_int32(src, y, 5) == 0, "failed to set y in export source");
  check(yices_model_set_bool(src, b, 1) == 0, "failed to set b in export source");
  check(yices_model_set_bv_from_array(src, bv_var, 4, bits) == 0, "failed to set bv in export source");
  check(yices_model_set_scalar(src, scalar_var, 7) == 0, "failed to set scalar in export source");

  check(yices_get_value(src, x, &xv) == 0, "failed to get x value");
  check(yices_get_value(src, y, &yv) == 0, "failed to get y value");
  check(yices_get_value(src, b, &bv) == 0, "failed to get bool value");
  check(yices_get_value(src, bv_var, &bv_src) == 0, "failed to get bv value");
  check(yices_get_value(src, scalar_var, &scalar_src) == 0, "failed to get scalar value");
  check(yices_get_value(src, yices_false(), &false_v) == 0, "failed to get false value");
  check(yices_get_value(src, yices_int32(0), &zero_v) == 0, "failed to get zero value");
  check(yices_get_value(src, yices_int32(1), &one_v) == 0, "failed to get one value");
  check(yices_get_value(src, yices_int32(5), &five_v) == 0, "failed to get five value");
  check(yices_get_value(src, yices_int32(11), &eleven_v) == 0, "failed to get eleven value");
  check(yices_get_value(src, yices_int32(13), &thirteen_v) == 0, "failed to get thirteen value");

  tuple_elem[0] = xv;
  tuple_elem[1] = yv;
  tuple_elem[2] = bv;
  check(yices_model_make_tuple(src, 3, tuple_elem, &tuple_src) == 0, "failed to build tuple source");
  map_args[0] = xv;
  map_args[1] = yv;
  check(yices_model_make_mapping(src, 2, map_args, &bv, &fun2_map) == 0, "failed to build function mapping");
  maps[0] = fun2_map;
  check(yices_model_make_function(src, fun2_type, 1, maps, &false_v, &fun2_src) == 0, "failed to build function source");

  check(yices_model_make_mapping(src, 1, &one_v, &eleven_v, &map1_src) == 0, "failed to build update base mapping");
  maps[0] = map1_src;
  check(yices_model_make_function(src, fun1_type, 1, maps, &zero_v, &fun1_src) == 0, "failed to build update base function");
  src_vtbl = model_get_vtbl(src);
  update_arg[0] = five_v.node_id;
  update = vtbl_mk_update(src_vtbl, fun1_src.node_id, 1, update_arg, thirteen_v.node_id);
  get_yval(src_vtbl, update, &update_src);

  check(yices_model_export_value(src, dst, &xv, &int_dst) == 0, "failed to export int value");
  check(yices_model_export_value(src, dst, &tuple_src, &tuple_dst) == 0, "failed to export tuple value");
  check(yices_model_export_value(src, dst, &fun2_src, &fun2_dst) == 0, "failed to export function value");
  check(yices_model_export_value(src, dst, &update_src, &update_dst) == 0, "failed to export update value");
  check(yices_model_export_value(src, dst, &bv_src, &bv_dst) == 0, "failed to export bitvector value");
  check(yices_model_export_value(src, dst, &scalar_src, &scalar_dst) == 0, "failed to export scalar value");

  yices_free_model(src);

  check_int_yval(dst, &int_dst, 3, "exported int value is wrong");
  check(yices_val_expand_tuple(dst, &tuple_dst, tuple_child) == 0, "failed to expand exported tuple");
  check_int_yval(dst, &tuple_child[0], 3, "exported tuple first child is wrong");
  check_int_yval(dst, &tuple_child[1], 5, "exported tuple second child is wrong");
  check_bool_yval(dst, &tuple_child[2], 1, "exported tuple third child is wrong");
  check(yices_val_get_bv(dst, &bv_dst, out_bits) == 0, "failed to inspect exported bitvector");
  check(out_bits[0] == 1 && out_bits[1] == 0 && out_bits[2] == 1 && out_bits[3] == 1,
        "exported bitvector is wrong");
  check(yices_val_get_scalar(dst, &scalar_dst, &scalar_idx, &scalar_type) == 0,
        "failed to inspect exported scalar");
  check(scalar_idx == 7 && scalar_type == uninterpreted_type, "exported scalar is wrong");

  g = yices_new_uninterpreted_term(fun2_type);
  check(yices_model_set_yval(dst, g, &fun2_dst) == 0, "failed to assign exported function");
  app = yices_application2(g, yices_int32(3), yices_int32(5));
  check(yices_get_bool_value(dst, app, &bval) == 0 && bval == 1, "exported function mapping is wrong");
  app = yices_application2(g, yices_int32(5), yices_int32(3));
  check(yices_get_bool_value(dst, app, &bval) == 0 && bval == 0, "exported function default is wrong");

  h = yices_new_uninterpreted_term(fun1_type);
  check(yices_model_set_yval(dst, h, &update_dst) == 0, "failed to assign exported update");
  app = yices_application1(h, yices_int32(1));
  check(yices_get_int32_value(dst, app, &ival) == 0 && ival == 11, "exported update base mapping is wrong");
  app = yices_application1(h, yices_int32(5));
  check(yices_get_int32_value(dst, app, &ival) == 0 && ival == 13, "exported update mapping is wrong");
  app = yices_application1(h, yices_int32(2));
  check(yices_get_int32_value(dst, app, &ival) == 0 && ival == 0, "exported update default is wrong");

  yices_free_model(dst);
}

int main(void) {
  yices_init();

  test_collect_defined_terms_named_and_unnamed();
  test_collect_defined_terms_ignores_negative_keys();
  test_collect_defined_terms_alias_domain_only();
  test_export_value_source_free_composites();

  yices_exit();

  return 0;
}
