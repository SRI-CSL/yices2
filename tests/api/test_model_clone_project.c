/*
 * Tests for model clone/project support and adjacent model-domain behavior.
 */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "api/yices_globals.h"
#include "api/yval.h"
#include "model/models.h"
#include "yices.h"

static void check(bool cond, const char *msg) {
  if (!cond) {
    fprintf(stderr, "%s\n", msg);
    fflush(stderr);
    yices_print_error(stderr);
    exit(2);
  }
}

static void run_named_test(const char *name, void (*test)(void)) {
  fprintf(stderr, "BEGIN %s\n", name);
  fflush(stderr);
  test();
  fprintf(stderr, "END %s\n", name);
  fflush(stderr);
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

static value_t make_constant_function(model_t *mdl, type_t fun_type, int32_t value) {
  value_table_t *vtbl;
  value_t def;

  vtbl = model_get_vtbl(mdl);
  def = vtbl_mk_int32(vtbl, value);
  return vtbl_mk_constant_function(vtbl, fun_type, def);
}

static value_t make_zero_div_function(model_t *mdl, int32_t value) {
  type_t real_type;

  real_type = yices_real_type();
  return make_constant_function(mdl, yices_function_type1(real_type, real_type), value);
}

static value_t make_int_zero_div_function(model_t *mdl, int32_t value) {
  type_t int_type;

  int_type = yices_int_type();
  return make_constant_function(mdl, yices_function_type1(int_type, int_type), value);
}

static void make_constant_function_yval(model_t *mdl, type_t fun_type, int32_t value, yval_t *fun) {
  get_yval(model_get_vtbl(mdl), make_constant_function(mdl, fun_type, value), fun);
}

static void make_update_function_yval(model_t *mdl, type_t fun_type, int32_t default_value,
                                      int32_t arg_value, int32_t mapped_value, yval_t *fun) {
  value_table_t *vtbl;
  value_t base, args[1], value;

  vtbl = model_get_vtbl(mdl);
  base = make_constant_function(mdl, fun_type, default_value);
  args[0] = vtbl_mk_int32(vtbl, arg_value);
  value = vtbl_mk_int32(vtbl, mapped_value);
  get_yval(vtbl, vtbl_mk_update(vtbl, base, 1, args, value), fun);
}

static void check_constant_function_yval(model_t *mdl, const yval_t *fun, type_t expected_type,
                                         int32_t expected_value, const char *msg) {
  yval_vector_t mappings;
  yval_t def;

  check(yices_val_function_type(mdl, fun) == expected_type, msg);
  yices_init_yval_vector(&mappings);
  check(yices_val_expand_function(mdl, fun, &def, &mappings) == 0, msg);
  check(mappings.size == 0, msg);
  check_int_yval(mdl, &def, expected_value, msg);
  yices_delete_yval_vector(&mappings);
}

static void check_unary_update_function_yval(model_t *mdl, const yval_t *fun, type_t expected_type,
                                             int32_t expected_default, int32_t expected_arg,
                                             int32_t expected_value, const char *msg) {
  yval_vector_t mappings;
  yval_t def, arg[1], value;

  check(yices_val_function_type(mdl, fun) == expected_type, msg);
  yices_init_yval_vector(&mappings);
  check(yices_val_expand_function(mdl, fun, &def, &mappings) == 0, msg);
  check(mappings.size == 1, msg);
  check_int_yval(mdl, &def, expected_default, msg);
  check(yices_val_expand_mapping(mdl, mappings.data, arg, &value) == 0, msg);
  check_int_yval(mdl, arg, expected_arg, msg);
  check_int_yval(mdl, &value, expected_value, msg);
  yices_delete_yval_vector(&mappings);
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

static void test_model_clone_defined_values_source_free(void) {
  model_t *src, *clone;
  term_vector_t v;
  term_t x, y;
  int32_t value;

  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());

  src = yices_new_model();
  check(src != NULL, "failed to create clone source");
  check(yices_model_set_int32(src, x, 11) == 0, "failed to set clone source x");
  check(yices_model_set_int32(src, y, 22) == 0, "failed to set clone source y");

  clone = yices_model_clone(src);
  check(clone != NULL, "failed to clone model");
  check(clone != src, "clone returned the source model");

  yices_free_model(src);

  check(yices_get_int32_value(clone, x, &value) == 0 && value == 11, "clone lost x value");
  check(yices_get_int32_value(clone, y, &value) == 0 && value == 22, "clone lost y value");

  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(clone, &v);
  check(v.size == 2, "clone has wrong defined-term count");
  check(vector_has_term(&v, x), "clone missing x");
  check(vector_has_term(&v, y), "clone missing y");
  yices_delete_term_vector(&v);

  yices_free_model(clone);
}

static void test_model_clone_preserves_alias_structure(void) {
  model_t *src, *clone;
  term_vector_t v;
  term_t x, y, x_plus_one;
  int32_t value;
  uint32_t src_map_size, src_alias_size;

  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  x_plus_one = yices_add(x, yices_int32(1));
  check(x_plus_one != NULL_TERM, "failed to build alias RHS");

  src = yices_new_model();
  check(src != NULL, "failed to create alias clone source");
  model_add_substitution(src, y, x_plus_one);
  src_map_size = src->map.nelems;
  src_alias_size = src->alias_map->nelems;

  clone = yices_model_clone(src);
  check(clone != NULL, "failed to clone alias model");

  check(src->has_alias && src->alias_map != NULL, "clone mutated source alias mode");
  check(src->map.nelems == src_map_size, "clone mutated source map");
  check(src->alias_map->nelems == src_alias_size, "clone mutated source alias map");

  check(clone->has_alias, "clone did not preserve alias mode");
  check(clone->alias_map != NULL, "clone did not preserve alias map");
  check(clone->map.nelems == src_map_size, "clone changed concrete map size");
  check(clone->alias_map->nelems == src_alias_size, "clone changed alias map size");
  check(model_find_term_substitution(clone, y) == x_plus_one, "clone lost alias substitution");
  check(model_find_term_value(clone, y) == null_value, "clone materialized alias-domain term");

  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(src, &v);
  check(v.size == 1 && vector_has_term(&v, y) && !vector_has_term(&v, x),
        "source alias defined terms are wrong");
  yices_reset_term_vector(&v);
  yices_model_collect_defined_terms(clone, &v);
  check(v.size == 1 && vector_has_term(&v, y) && !vector_has_term(&v, x),
        "clone alias defined terms are wrong");
  yices_delete_term_vector(&v);

  yices_free_model(src);

  check(yices_get_int32_value(clone, y, &value) == 0 && value == 1, "clone alias value is wrong");
  check(yices_get_int32_value(clone, x, &value) == 0 && value == 0, "clone default value is wrong");

  yices_free_model(clone);
}

static void test_model_clone_preserves_zero_division_slots(void) {
  model_t *src, *clone;
  value_table_t *src_vtbl, *clone_vtbl;
  term_t div;
  int32_t value;

  src = yices_new_model();
  check(src != NULL, "failed to create zero-div clone source");

  src_vtbl = model_get_vtbl(src);
  vtbl_set_zero_rdiv(src_vtbl, make_zero_div_function(src, 17));
  vtbl_set_zero_idiv(src_vtbl, make_int_zero_div_function(src, 23));
  vtbl_set_zero_mod(src_vtbl, make_int_zero_div_function(src, 29));

  clone = yices_model_clone(src);
  check(clone != NULL, "failed to clone zero-div model");
  clone_vtbl = model_get_vtbl(clone);
  check(clone_vtbl->zero_rdiv_fun != null_value, "clone lost zero-rdiv slot");
  check(clone_vtbl->zero_idiv_fun != null_value, "clone lost zero-idiv slot");
  check(clone_vtbl->zero_mod_fun != null_value, "clone lost zero-mod slot");

  yices_free_model(src);

  div = yices_division(yices_int32(5), yices_zero());
  check(yices_get_int32_value(clone, div, &value) == 0 && value == 17,
        "clone zero-rdiv value is wrong");
  div = yices_idiv(yices_int32(5), yices_zero());
  check(yices_get_int32_value(clone, div, &value) == 0 && value == 23,
        "clone zero-idiv value is wrong");
  div = yices_imod(yices_int32(5), yices_zero());
  check(yices_get_int32_value(clone, div, &value) == 0 && value == 29,
        "clone zero-mod value is wrong");

  yices_free_model(clone);
}

static void test_model_zero_div_getters_default_non_mutating(void) {
  model_t *mdl;
  value_table_t *vtbl;
  yval_t rdiv, idiv, mod, explicit_fun;
  type_t real_type, int_type, rr_fun_type, ii_fun_type;

  real_type = yices_real_type();
  int_type = yices_int_type();
  rr_fun_type = yices_function_type1(real_type, real_type);
  ii_fun_type = yices_function_type1(int_type, int_type);

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create zero-div getter model");
  vtbl = model_get_vtbl(mdl);

  check(yices_model_get_zero_rdiv_function(mdl, &rdiv) == 0, "failed to get default zero-rdiv");
  check(yices_model_get_zero_idiv_function(mdl, &idiv) == 0, "failed to get default zero-idiv");
  check(yices_model_get_zero_mod_function(mdl, &mod) == 0, "failed to get default zero-mod");

  check(vtbl->zero_rdiv_fun == null_value, "zero-rdiv getter installed default");
  check(vtbl->zero_idiv_fun == null_value, "zero-idiv getter installed default");
  check(vtbl->zero_mod_fun == null_value, "zero-mod getter installed default");

  check_constant_function_yval(mdl, &rdiv, rr_fun_type, 0, "default zero-rdiv function is wrong");
  check_constant_function_yval(mdl, &idiv, ii_fun_type, 0, "default zero-idiv function is wrong");
  check_constant_function_yval(mdl, &mod, ii_fun_type, 0, "default zero-mod function is wrong");

  make_constant_function_yval(mdl, rr_fun_type, 17, &explicit_fun);
  check(yices_model_set_zero_rdiv_function(mdl, &explicit_fun) == 0,
        "zero-rdiv setter failed after getter");
  check(vtbl->zero_rdiv_fun != null_value, "zero-rdiv setter did not install explicit function");

  yices_free_model(mdl);
}

static void test_model_zero_div_installed_defaults_have_api_types(void) {
  model_t *mdl;
  value_table_t *vtbl;
  yval_t rdiv, idiv, mod;
  type_t real_type, int_type, rr_fun_type, ii_fun_type;

  real_type = yices_real_type();
  int_type = yices_int_type();
  rr_fun_type = yices_function_type1(real_type, real_type);
  ii_fun_type = yices_function_type1(int_type, int_type);

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create zero-div default model");
  vtbl = model_get_vtbl(mdl);

  vtbl_set_default_zero_divide(vtbl);
  check(vtbl->zero_rdiv_fun != null_value, "default helper did not set zero-rdiv");
  check(vtbl->zero_idiv_fun != null_value, "default helper did not set zero-idiv");
  check(vtbl->zero_mod_fun != null_value, "default helper did not set zero-mod");

  check(yices_model_get_zero_rdiv_function(mdl, &rdiv) == 0, "failed to get installed zero-rdiv");
  check(yices_model_get_zero_idiv_function(mdl, &idiv) == 0, "failed to get installed zero-idiv");
  check(yices_model_get_zero_mod_function(mdl, &mod) == 0, "failed to get installed zero-mod");

  check_constant_function_yval(mdl, &rdiv, rr_fun_type, 0, "installed zero-rdiv function is wrong");
  check_constant_function_yval(mdl, &idiv, ii_fun_type, 0, "installed zero-idiv function is wrong");
  check_constant_function_yval(mdl, &mod, ii_fun_type, 0, "installed zero-mod function is wrong");

  yices_free_model(mdl);
}

static void test_model_zero_div_setters_and_getters(void) {
  model_t *mdl;
  value_table_t *vtbl;
  yval_t rdiv, idiv, mod;
  term_t div;
  type_t real_type, int_type, rr_fun_type, ii_fun_type;
  int32_t value;

  real_type = yices_real_type();
  int_type = yices_int_type();
  rr_fun_type = yices_function_type1(real_type, real_type);
  ii_fun_type = yices_function_type1(int_type, int_type);

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create zero-div setter model");
  vtbl = model_get_vtbl(mdl);

  make_constant_function_yval(mdl, rr_fun_type, 17, &rdiv);
  make_constant_function_yval(mdl, ii_fun_type, 23, &idiv);
  make_constant_function_yval(mdl, ii_fun_type, 29, &mod);

  check(yices_model_set_zero_rdiv_function(mdl, &rdiv) == 0, "failed to set zero-rdiv");
  check(yices_model_set_zero_idiv_function(mdl, &idiv) == 0, "failed to set zero-idiv");
  check(yices_model_set_zero_mod_function(mdl, &mod) == 0, "failed to set zero-mod");
  check(vtbl->zero_rdiv_fun != null_value, "zero-rdiv slot is unset");
  check(vtbl->zero_idiv_fun != null_value, "zero-idiv slot is unset");
  check(vtbl->zero_mod_fun != null_value, "zero-mod slot is unset");

  check(yices_model_get_zero_rdiv_function(mdl, &rdiv) == 0, "failed to get explicit zero-rdiv");
  check(yices_model_get_zero_idiv_function(mdl, &idiv) == 0, "failed to get explicit zero-idiv");
  check(yices_model_get_zero_mod_function(mdl, &mod) == 0, "failed to get explicit zero-mod");
  check_constant_function_yval(mdl, &rdiv, rr_fun_type, 17, "explicit zero-rdiv function is wrong");
  check_constant_function_yval(mdl, &idiv, ii_fun_type, 23, "explicit zero-idiv function is wrong");
  check_constant_function_yval(mdl, &mod, ii_fun_type, 29, "explicit zero-mod function is wrong");

  div = yices_division(yices_int32(5), yices_zero());
  check(yices_get_int32_value(mdl, div, &value) == 0 && value == 17,
        "zero-rdiv evaluation is wrong");
  div = yices_idiv(yices_int32(5), yices_zero());
  check(yices_get_int32_value(mdl, div, &value) == 0 && value == 23,
        "zero-idiv evaluation is wrong");
  div = yices_imod(yices_int32(5), yices_zero());
  check(yices_get_int32_value(mdl, div, &value) == 0 && value == 29,
        "zero-mod evaluation is wrong");

  check(yices_model_set_zero_rdiv_function(mdl, &rdiv) == -1, "zero-rdiv setter overwrote slot");
  check(yices_error_code() == MDL_DUPLICATE_VAR, "zero-rdiv overwrite error is wrong");

  yices_free_model(mdl);
}

static void test_model_zero_div_setters_validate_function_type(void) {
  model_t *mdl;
  yval_t int_val, wrong_fun, good_fun;
  type_t real_type, int_type, rr_fun_type, ii_fun_type;

  real_type = yices_real_type();
  int_type = yices_int_type();
  rr_fun_type = yices_function_type1(real_type, real_type);
  ii_fun_type = yices_function_type1(int_type, int_type);

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create zero-div validation model");

  get_yval(model_get_vtbl(mdl), vtbl_mk_int32(model_get_vtbl(mdl), 0), &int_val);
  check(yices_model_set_zero_rdiv_function(mdl, &int_val) == -1,
        "zero-rdiv setter accepted non-function value");
  check(yices_error_code() == TYPE_MISMATCH, "zero-rdiv non-function error is wrong");
  check(model_get_vtbl(mdl)->zero_rdiv_fun == null_value, "zero-rdiv invalid setter changed slot");

  make_constant_function_yval(mdl, rr_fun_type, 13, &wrong_fun);
  check(yices_model_set_zero_idiv_function(mdl, &wrong_fun) == -1,
        "zero-idiv setter accepted wrong function type");
  check(yices_error_code() == TYPE_MISMATCH, "zero-idiv wrong-type error is wrong");
  check(model_get_vtbl(mdl)->zero_idiv_fun == null_value, "zero-idiv invalid setter changed slot");
  check(yices_model_set_zero_mod_function(mdl, &wrong_fun) == -1,
        "zero-mod setter accepted wrong function type");
  check(yices_error_code() == TYPE_MISMATCH, "zero-mod wrong-type error is wrong");
  check(model_get_vtbl(mdl)->zero_mod_fun == null_value, "zero-mod invalid setter changed slot");

  make_constant_function_yval(mdl, ii_fun_type, 19, &good_fun);
  check(yices_model_set_zero_idiv_function(mdl, &good_fun) == 0,
        "zero-idiv setter rejected correct function type");

  yices_free_model(mdl);
}

static void test_model_zero_div_setters_accept_updates(void) {
  model_t *mdl;
  yval_t update_fun, extracted;
  term_t div;
  type_t real_type, rr_fun_type;
  int32_t value;

  real_type = yices_real_type();
  rr_fun_type = yices_function_type1(real_type, real_type);

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create zero-div update model");

  make_update_function_yval(mdl, rr_fun_type, 0, 5, 31, &update_fun);
  check(yices_model_set_zero_rdiv_function(mdl, &update_fun) == 0,
        "zero-rdiv setter rejected update value");
  check(yices_model_get_zero_rdiv_function(mdl, &extracted) == 0,
        "failed to get zero-rdiv update value");
  check_unary_update_function_yval(mdl, &extracted, rr_fun_type, 0, 5, 31,
                                   "zero-rdiv update function is wrong");

  div = yices_division(yices_int32(5), yices_zero());
  check(yices_get_int32_value(mdl, div, &value) == 0 && value == 31,
        "zero-rdiv update evaluation is wrong");

  yices_free_model(mdl);
}

static void test_model_project_materializes_domain(void) {
  model_t *src, *projected, *empty;
  term_vector_t v;
  term_t x, y, z;
  term_t domain[1];
  int32_t value;

  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  z = yices_new_uninterpreted_term(yices_int_type());

  src = yices_new_model();
  check(src != NULL, "failed to create project source");
  check(yices_model_set_int32(src, x, 1) == 0, "failed to set project source x");
  check(yices_model_set_int32(src, y, 2) == 0, "failed to set project source y");
  check(yices_model_set_int32(src, z, 3) == 0, "failed to set project source z");

  domain[0] = y;
  projected = yices_model_project(src, 1, domain);
  check(projected != NULL, "failed to project model");
  check(!projected->has_alias && projected->alias_map == NULL, "projected model has aliases");
  check(yices_get_int32_value(projected, y, &value) == 0 && value == 2, "projected y value is wrong");
  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(projected, &v);
  check(v.size == 1 && vector_has_term(&v, y) && !vector_has_term(&v, x) && !vector_has_term(&v, z),
        "projected model has wrong initial defined terms");
  yices_reset_term_vector(&v);
  check(yices_model_set_int32(projected, x, 10) == 0, "failed to set omitted x after projection");
  check(yices_model_set_int32(projected, z, 30) == 0, "failed to set omitted z after projection");
  check(yices_model_set_int32(projected, y, 20) == -1, "projection allowed overwrite of y");
  check(yices_error_code() == MDL_DUPLICATE_VAR, "projection duplicate error is wrong");

  yices_model_collect_defined_terms(projected, &v);
  check(v.size == 3 && vector_has_term(&v, x) && vector_has_term(&v, y) && vector_has_term(&v, z),
        "projected model has wrong defined terms after extension");
  yices_delete_term_vector(&v);
  yices_free_model(projected);

  empty = yices_model_project(src, 0, NULL);
  check(empty != NULL, "failed to build empty projection");
  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(empty, &v);
  check(v.size == 0, "empty projection has defined terms");
  yices_delete_term_vector(&v);
  check(yices_model_set_int32(empty, x, 100) == 0, "failed to extend empty projection");
  yices_free_model(empty);

  yices_free_model(src);
}

static void test_model_project_alias_and_defaults(void) {
  model_t *src, *project_y, *project_x, *project_xy;
  term_vector_t v;
  term_t x, y, x_plus_one;
  term_t domain[2];
  int32_t value;
  uint32_t src_map_size, src_alias_size;

  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  x_plus_one = yices_add(x, yices_int32(1));
  check(x_plus_one != NULL_TERM, "failed to build project alias RHS");

  src = yices_new_model();
  check(src != NULL, "failed to create alias project source");
  model_add_substitution(src, y, x_plus_one);
  src_map_size = src->map.nelems;
  src_alias_size = src->alias_map->nelems;

  domain[0] = y;
  project_y = yices_model_project(src, 1, domain);
  check(project_y != NULL, "failed to project alias y");
  check(src->map.nelems == src_map_size && src->alias_map->nelems == src_alias_size,
        "project mutated source alias model");
  check(!project_y->has_alias && project_y->alias_map == NULL, "project y preserved aliases");
  check(model_find_term_value(project_y, y) != null_value, "project y did not materialize y");
  check(model_find_term_value(project_y, x) == null_value, "project y materialized alias dependency x");
  check(yices_get_int32_value(project_y, y, &value) == 0 && value == 1, "project y value is wrong");
  check(yices_model_set_int32(project_y, x, 7) == 0, "project y did not allow omitted x extension");
  check(yices_get_int32_value(project_y, x, &value) == 0 && value == 7, "project y extension value is wrong");
  yices_free_model(project_y);

  domain[0] = x;
  project_x = yices_model_project(src, 1, domain);
  check(project_x != NULL, "failed to project default x");
  check(!project_x->has_alias && project_x->alias_map == NULL, "project x preserved aliases");
  check(model_find_term_value(project_x, x) != null_value, "project x did not materialize x");
  check(model_find_term_value(project_x, y) == null_value, "project x materialized y");
  check(yices_get_int32_value(project_x, x, &value) == 0 && value == 0, "project x default is wrong");
  yices_free_model(project_x);

  domain[0] = x;
  domain[1] = y;
  project_xy = yices_model_project(src, 2, domain);
  check(project_xy != NULL, "failed to project x and y");
  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(project_xy, &v);
  check(v.size == 2 && vector_has_term(&v, x) && vector_has_term(&v, y),
        "project xy defined terms are wrong");
  yices_delete_term_vector(&v);
  check(yices_get_int32_value(project_xy, x, &value) == 0 && value == 0, "project xy x is wrong");
  check(yices_get_int32_value(project_xy, y, &value) == 0 && value == 1, "project xy y is wrong");
  yices_free_model(project_xy);

  yices_free_model(src);
}

static void test_model_project_domain_validation(void) {
  model_t *src, *projected;
  term_t x, b, invalid, duplicate[2];

  x = yices_new_uninterpreted_term(yices_int_type());
  b = yices_new_uninterpreted_term(yices_bool_type());

  src = yices_new_model();
  check(src != NULL, "failed to create validation project source");

  projected = yices_model_project(src, 1, NULL);
  check(projected == NULL, "project accepted NULL non-empty domain");
  check(yices_error_code() == INVALID_TERM, "NULL-domain error is wrong");

  invalid = yices_not(b);
  projected = yices_model_project(src, 1, &invalid);
  check(projected == NULL, "project accepted negative domain term");
  check(yices_error_code() == MDL_UNINT_REQUIRED, "negative-domain error is wrong");

  invalid = yices_add(x, yices_int32(1));
  projected = yices_model_project(src, 1, &invalid);
  check(projected == NULL, "project accepted non-uninterpreted domain term");
  check(yices_error_code() == MDL_UNINT_REQUIRED, "non-uninterpreted-domain error is wrong");

  duplicate[0] = x;
  duplicate[1] = x;
  projected = yices_model_project(src, 2, duplicate);
  check(projected == NULL, "project accepted duplicate domain term");
  check(yices_error_code() == MDL_DUPLICATE_VAR, "duplicate-domain error is wrong");

  yices_free_model(src);
}

static void test_model_project_evaluation_failure(void) {
  model_t *src, *projected;
  term_t y, var, quantified;
  term_t vars[1], domain[1];
  uint32_t src_map_size, src_alias_size;

  fprintf(stderr, "  build quantified alias\n");
  fflush(stderr);
  y = yices_new_uninterpreted_term(yices_bool_type());
  var = yices_new_variable(yices_bool_type());
  vars[0] = var;
  quantified = yices_forall(1, vars, var);
  check(quantified != NULL_TERM, "failed to build quantified alias target");

  fprintf(stderr, "  install quantified alias\n");
  fflush(stderr);
  src = yices_new_model();
  check(src != NULL, "failed to create eval-failure project source");
  model_add_substitution(src, y, quantified);
  src_map_size = src->map.nelems;
  src_alias_size = src->alias_map->nelems;

  fprintf(stderr, "  project quantified alias\n");
  fflush(stderr);
  domain[0] = y;
  projected = yices_model_project(src, 1, domain);
  fprintf(stderr, "  project returned %p error %d\n", (void *) projected, yices_error_code());
  fflush(stderr);
  check(projected == NULL, "project accepted unevaluable alias target");
  check(yices_error_code() == EVAL_QUANTIFIER, "project eval-failure error is wrong");
  check(src->map.nelems == src_map_size && src->alias_map->nelems == src_alias_size,
        "project eval failure mutated source");

  yices_free_model(src);
}

static void test_model_set_flattens_alias_before_append(void) {
  model_t *mdl;
  term_vector_t v;
  term_t x, y, x_plus_one;
  int32_t value;

  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  x_plus_one = yices_add(x, yices_int32(1));
  check(x_plus_one != NULL_TERM, "failed to build setter alias RHS");

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create setter alias model");
  model_add_substitution(mdl, y, x_plus_one);

  check(yices_model_set_int32(mdl, x, 7) == 0, "failed to append omitted alias dependency");
  check(mdl->alias_map == NULL, "setter append did not clear aliases");
  check(model_find_term_value(mdl, y) != null_value, "setter append did not materialize alias domain");
  check(yices_get_int32_value(mdl, y, &value) == 0 && value == 1,
        "setter append did not freeze alias value before append");
  check(yices_get_int32_value(mdl, x, &value) == 0 && value == 7,
        "setter append lost appended value");

  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(mdl, &v);
  check(v.size == 2 && vector_has_term(&v, x) && vector_has_term(&v, y),
        "setter append has wrong flattened defined terms");
  yices_delete_term_vector(&v);

  yices_free_model(mdl);
}

static void test_model_set_rejects_alias_duplicate(void) {
  model_t *mdl;
  term_vector_t v;
  term_t x, y, x_plus_one;
  int32_t value;

  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  x_plus_one = yices_add(x, yices_int32(1));
  check(x_plus_one != NULL_TERM, "failed to build setter duplicate alias RHS");

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create setter duplicate alias model");
  model_add_substitution(mdl, y, x_plus_one);

  check(yices_model_set_int32(mdl, y, 99) == -1, "setter overwrote alias-defined term");
  check(yices_error_code() == MDL_DUPLICATE_VAR, "setter alias duplicate error is wrong");
  check(mdl->alias_map == NULL, "setter duplicate did not clear aliases");
  check(model_find_term_value(mdl, y) != null_value, "setter duplicate did not materialize alias domain");
  check(model_find_term_value(mdl, x) == null_value, "setter duplicate materialized alias dependency");
  check(yices_get_int32_value(mdl, y, &value) == 0 && value == 1,
        "setter duplicate changed alias value");

  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(mdl, &v);
  check(v.size == 1 && vector_has_term(&v, y) && !vector_has_term(&v, x),
        "setter duplicate has wrong flattened defined terms");
  yices_delete_term_vector(&v);

  check(yices_model_set_int32(mdl, x, 7) == 0, "failed to append omitted dependency after duplicate");
  check(yices_get_int32_value(mdl, x, &value) == 0 && value == 7,
        "setter duplicate follow-up append is wrong");

  yices_free_model(mdl);
}

static void test_model_set_flatten_failure_is_atomic(void) {
  model_t *mdl;
  term_t x, y, var, quantified;
  term_t vars[1];
  uint32_t map_size, alias_size;

  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_bool_type());
  var = yices_new_variable(yices_bool_type());
  vars[0] = var;
  quantified = yices_forall(1, vars, var);
  check(quantified != NULL_TERM, "failed to build setter failure alias target");

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create setter failure model");
  model_add_substitution(mdl, y, quantified);
  map_size = mdl->map.nelems;
  alias_size = mdl->alias_map->nelems;

  check(yices_model_set_int32(mdl, x, 4) == -1, "setter append ignored alias flatten failure");
  check(yices_error_code() == EVAL_QUANTIFIER, "setter flatten failure error is wrong");
  check(mdl->map.nelems == map_size, "setter flatten failure mutated map");
  check(mdl->alias_map != NULL && mdl->alias_map->nelems == alias_size,
        "setter flatten failure mutated alias map");
  check(model_find_term_value(mdl, x) == null_value, "setter flatten failure appended target");
  check(model_find_term_substitution(mdl, y) == quantified, "setter flatten failure lost alias");

  yices_free_model(mdl);
}

static void test_model_set_invalid_value_does_not_flatten_alias(void) {
  model_t *mdl;
  term_t x, y, x_plus_one, bv;
  int32_t bits[3];
  uint32_t map_size, alias_size;

  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  x_plus_one = yices_add(x, yices_int32(1));
  check(x_plus_one != NULL_TERM, "failed to build setter invalid-value alias RHS");
  bv = yices_new_uninterpreted_term(yices_bv_type(4));

  bits[0] = 1;
  bits[1] = 0;
  bits[2] = 1;

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create setter invalid-value model");
  model_add_substitution(mdl, y, x_plus_one);
  map_size = mdl->map.nelems;
  alias_size = mdl->alias_map->nelems;

  check(yices_model_set_bv_from_array(mdl, bv, 3, bits) == -1,
        "setter accepted invalid bitvector value");
  check(yices_error_code() == INCOMPATIBLE_BVSIZES, "setter invalid-value error is wrong");
  check(mdl->map.nelems == map_size, "setter invalid value mutated map");
  check(mdl->alias_map != NULL && mdl->alias_map->nelems == alias_size,
        "setter invalid value flattened aliases");
  check(model_find_term_substitution(mdl, y) == x_plus_one, "setter invalid value lost alias");

  yices_free_model(mdl);
}

int main(void) {
  yices_init();

  run_named_test("test_collect_defined_terms_named_and_unnamed",
                 test_collect_defined_terms_named_and_unnamed);
  run_named_test("test_collect_defined_terms_ignores_negative_keys",
                 test_collect_defined_terms_ignores_negative_keys);
  run_named_test("test_collect_defined_terms_alias_domain_only",
                 test_collect_defined_terms_alias_domain_only);
  run_named_test("test_export_value_source_free_composites",
                 test_export_value_source_free_composites);
  run_named_test("test_model_clone_defined_values_source_free",
                 test_model_clone_defined_values_source_free);
  run_named_test("test_model_clone_preserves_alias_structure",
                 test_model_clone_preserves_alias_structure);
  run_named_test("test_model_clone_preserves_zero_division_slots",
                 test_model_clone_preserves_zero_division_slots);
  run_named_test("test_model_zero_div_getters_default_non_mutating",
                 test_model_zero_div_getters_default_non_mutating);
  run_named_test("test_model_zero_div_installed_defaults_have_api_types",
                 test_model_zero_div_installed_defaults_have_api_types);
  run_named_test("test_model_zero_div_setters_and_getters",
                 test_model_zero_div_setters_and_getters);
  run_named_test("test_model_zero_div_setters_validate_function_type",
                 test_model_zero_div_setters_validate_function_type);
  run_named_test("test_model_zero_div_setters_accept_updates",
                 test_model_zero_div_setters_accept_updates);
  run_named_test("test_model_project_materializes_domain",
                 test_model_project_materializes_domain);
  run_named_test("test_model_project_alias_and_defaults",
                 test_model_project_alias_and_defaults);
  run_named_test("test_model_project_domain_validation",
                 test_model_project_domain_validation);
  run_named_test("test_model_project_evaluation_failure",
                 test_model_project_evaluation_failure);
  run_named_test("test_model_set_flattens_alias_before_append",
                 test_model_set_flattens_alias_before_append);
  run_named_test("test_model_set_rejects_alias_duplicate",
                 test_model_set_rejects_alias_duplicate);
  run_named_test("test_model_set_flatten_failure_is_atomic",
                 test_model_set_flatten_failure_is_atomic);
  run_named_test("test_model_set_invalid_value_does_not_flatten_alias",
                 test_model_set_invalid_value_does_not_flatten_alias);

  yices_exit();

  return 0;
}
