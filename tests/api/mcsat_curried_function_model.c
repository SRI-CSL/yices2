#include <assert.h>
#include <string.h>

#include "yices.h"

static context_t* make_mcsat_context(void) {
  ctx_config_t* cfg = yices_new_config();
  assert(cfg != NULL);
  assert(yices_set_config(cfg, "solver-type", "mcsat") == 0);
  assert(yices_set_config(cfg, "mode", "interactive") == 0);
  assert(yices_set_config(cfg, "model-interpolation", "true") == 0);

  context_t* ctx = yices_new_context(cfg);
  yices_free_config(cfg);
  assert(ctx != NULL);
  return ctx;
}

int main(void) {
  int32_t app2_value;
  int32_t status;
  term_t formula;
  yval_t app1_value;

  if (! yices_has_mcsat()) {
    return 1; // skipped
  }

  yices_init();

  type_t int_type = yices_int_type();
  type_t inner_fun_type = yices_function_type1(int_type, int_type);
  type_t outer_fun_type = yices_function_type1(int_type, inner_fun_type);

  term_t array = yices_new_uninterpreted_term(outer_fun_type);
  yices_set_term_name(array, "array");

  term_t args1[1] = { yices_int32(1) };
  term_t app1 = yices_application(array, 1, args1);
  term_t args2[1] = { yices_int32(7) };
  term_t app2 = yices_application(app1, 1, args2);
  formula = yices_eq(app2, yices_int32(10));

  context_t* ctx = make_mcsat_context();
  assert(yices_assert_formula(ctx, formula) == 0);
  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);

  model_t* model = yices_get_model(ctx, 1);
  assert(model != NULL);

  char* model_str = yices_model_to_string(model, 120, 80, 0);
  assert(model_str != NULL);
  assert(strstr(model_str, "array") != NULL);
  assert(strstr(model_str, "10") != NULL);

  status = yices_get_value(model, app1, &app1_value);
  assert(status == 0);
  if (status != 0 || app1_value.node_tag != YVAL_FUNCTION) {
    return 2;
  }

  status = yices_get_int32_value(model, app2, &app2_value);
  assert(status == 0);
  if (status != 0 || app2_value != 10) {
    return 3;
  }

  yices_free_string(model_str);
  yices_free_model(model);
  yices_free_context(ctx);
  yices_exit();

  return 0;
}
