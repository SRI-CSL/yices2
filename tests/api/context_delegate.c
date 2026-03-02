#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

#include <yices.h>

static context_t *new_qfbv_one_shot_context(void) {
  ctx_config_t *config;
  context_t *ctx;

  config = yices_new_config();
  assert(config != NULL);

  assert(yices_default_config_for_logic(config, "QF_BV") == 0);
  assert(yices_set_config(config, "mode", "one-shot") == 0);

  ctx = yices_new_context(config);
  assert(ctx != NULL);

  yices_free_config(config);
  return ctx;
}

static context_t *new_qflia_one_shot_context(void) {
  ctx_config_t *config;
  context_t *ctx;

  config = yices_new_config();
  assert(config != NULL);

  assert(yices_default_config_for_logic(config, "QF_LIA") == 0);
  assert(yices_set_config(config, "mode", "one-shot") == 0);

  ctx = yices_new_context(config);
  assert(ctx != NULL);

  yices_free_config(config);
  return ctx;
}

static context_t *new_qfbv_pushpop_context(void) {
  ctx_config_t *config;
  context_t *ctx;

  config = yices_new_config();
  assert(config != NULL);

  assert(yices_default_config_for_logic(config, "QF_BV") == 0);
  assert(yices_set_config(config, "mode", "push-pop") == 0);

  ctx = yices_new_context(config);
  assert(ctx != NULL);

  yices_free_config(config);
  return ctx;
}

static param_t *new_delegate_params(const char *delegate) {
  param_t *params;

  params = yices_new_param_record();
  assert(params != NULL);
  assert(yices_set_param(params, "delegate", delegate) == 0);

  return params;
}

static void check_sat_case(const char *delegate) {
  type_t bv8;
  term_t x, f;
  context_t *ctx;
  param_t *params;
  smt_status_t stat;
  model_t *mdl;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);
  f = yices_bveq_atom(yices_bvadd(x, yices_bvconst_uint32(8, 1)), yices_bvconst_uint32(8, 2));

  ctx = new_qfbv_one_shot_context();
  assert(yices_assert_formula(ctx, f) == 0);

  params = new_delegate_params(delegate);
  stat = yices_check_context(ctx, params);
  assert(stat == YICES_STATUS_SAT);
  assert(yices_error_code() == YICES_NO_ERROR);

  mdl = yices_get_model(ctx, 1);
  assert(mdl != NULL);
  yices_free_model(mdl);
  yices_free_param_record(params);
  yices_free_context(ctx);
}

static void check_unsat_case(const char *delegate) {
  type_t bv8;
  term_t x, f0, f1;
  context_t *ctx;
  param_t *params;
  smt_status_t stat;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);

  f0 = yices_bveq_atom(x, yices_bvconst_uint32(8, 0));
  f1 = yices_bveq_atom(x, yices_bvconst_uint32(8, 1));

  ctx = new_qfbv_one_shot_context();
  assert(yices_assert_formula(ctx, f0) == 0);
  assert(yices_assert_formula(ctx, f1) == 0);

  params = new_delegate_params(delegate);
  stat = yices_check_context(ctx, params);
  assert(stat == YICES_STATUS_UNSAT);
  assert(yices_error_code() == YICES_NO_ERROR);

  yices_free_param_record(params);
  yices_free_context(ctx);
}

int main(void) {
  const char *delegates[] = { "y2sat", "cadical", "cryptominisat", "kissat" };
  context_t *ctx;
  param_t *params;
  smt_status_t stat;
  uint32_t i;

  yices_init();

  assert(yices_has_delegate("y2sat"));

  for (i=0; i<sizeof(delegates)/sizeof(delegates[0]); i++) {
    if (yices_has_delegate(delegates[i])) {
      check_sat_case(delegates[i]);
      check_unsat_case(delegates[i]);
    }
  }

  // Unknown delegate (rejected by yices_set_param)
  params = yices_new_param_record();
  assert(params != NULL);
  assert(yices_set_param(params, "delegate", "not-a-delegate") == -1);
  assert(yices_error_code() == CTX_INVALID_PARAMETER_VALUE);
  yices_free_param_record(params);

  // Known delegate that's not enabled in this build
  if (!yices_has_delegate("cadical")) {
    ctx = new_qfbv_one_shot_context();
    params = new_delegate_params("cadical");
    stat = yices_check_context(ctx, params);
    assert(stat == YICES_STATUS_ERROR);
    assert(yices_error_code() == CTX_DELEGATE_NOT_AVAILABLE);
    yices_free_param_record(params);
    yices_free_context(ctx);
  }

  // Wrong mode: push-pop
  ctx = new_qfbv_pushpop_context();
  params = new_delegate_params("y2sat");
  stat = yices_check_context(ctx, params);
  assert(stat == YICES_STATUS_ERROR);
  assert(yices_error_code() == CTX_OPERATION_NOT_SUPPORTED);
  yices_free_param_record(params);
  yices_free_context(ctx);

  // Wrong logic: not QF_BV
  ctx = new_qflia_one_shot_context();
  params = new_delegate_params("y2sat");
  stat = yices_check_context(ctx, params);
  assert(stat == YICES_STATUS_ERROR);
  assert(yices_error_code() == CTX_OPERATION_NOT_SUPPORTED);
  yices_free_param_record(params);
  yices_free_context(ctx);

  yices_exit();
  return 0;
}
