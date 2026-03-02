#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

#include <yices.h>

static void expect_status(context_t *ctx, const param_t *params, smt_status_t expected) {
  smt_status_t stat;

  stat = yices_check_context(ctx, params);
  assert(stat == expected);
  assert(yices_error_code() == YICES_NO_ERROR);
}

static void assert_formula_true_in_context_model(context_t *ctx, term_t f) {
  model_t *mdl;

  mdl = yices_get_model(ctx, 1);
  assert(mdl != NULL);
  assert(yices_formula_true_in_model(mdl, f) == 1);
  yices_free_model(mdl);
}

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

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);
  f = yices_bveq_atom(yices_bvadd(x, yices_bvconst_uint32(8, 1)), yices_bvconst_uint32(8, 2));

  ctx = new_qfbv_one_shot_context();
  assert(yices_assert_formula(ctx, f) == 0);

  params = new_delegate_params(delegate);
  expect_status(ctx, params, YICES_STATUS_SAT);
  assert_formula_true_in_context_model(ctx, f);
  yices_free_param_record(params);
  yices_free_context(ctx);
}

static void check_unsat_case(const char *delegate) {
  type_t bv8;
  term_t x, f0, f1;
  context_t *ctx;
  param_t *params;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);

  f0 = yices_bveq_atom(x, yices_bvconst_uint32(8, 0));
  f1 = yices_bveq_atom(x, yices_bvconst_uint32(8, 1));

  ctx = new_qfbv_one_shot_context();
  assert(yices_assert_formula(ctx, f0) == 0);
  assert(yices_assert_formula(ctx, f1) == 0);

  params = new_delegate_params(delegate);
  expect_status(ctx, params, YICES_STATUS_UNSAT);

  yices_free_param_record(params);
  yices_free_context(ctx);
}

static void check_pushpop_incremental_case(const char *delegate) {
  type_t bv8;
  term_t x, f0, f1;
  context_t *ctx;
  param_t *params;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);

  f0 = yices_bveq_atom(x, yices_bvconst_uint32(8, 0));
  f1 = yices_bveq_atom(x, yices_bvconst_uint32(8, 1));

  ctx = new_qfbv_pushpop_context();
  params = new_delegate_params(delegate);

  assert(yices_assert_formula(ctx, f0) == 0);
  expect_status(ctx, params, YICES_STATUS_SAT);

  assert(yices_push(ctx) == 0);
  assert(yices_assert_formula(ctx, f1) == 0);
  expect_status(ctx, params, YICES_STATUS_UNSAT);

  assert(yices_pop(ctx) == 0);
  expect_status(ctx, params, YICES_STATUS_SAT);

  assert(yices_assert_formula(ctx, f1) == 0);
  expect_status(ctx, params, YICES_STATUS_UNSAT);

  yices_free_param_record(params);
  yices_free_context(ctx);
}

static void check_sat_model_value_case(const char *delegate) {
  type_t bv8;
  term_t x, f0, f1;
  context_t *ctx;
  param_t *params;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);
  f0 = yices_bveq_atom(yices_bvadd(x, yices_bvconst_uint32(8, 1)), yices_bvconst_uint32(8, 2));
  f1 = yices_bveq_atom(x, yices_bvconst_uint32(8, 1));

  ctx = new_qfbv_one_shot_context();
  assert(yices_assert_formula(ctx, f0) == 0);

  params = new_delegate_params(delegate);
  expect_status(ctx, params, YICES_STATUS_SAT);
  assert_formula_true_in_context_model(ctx, f0);
  assert_formula_true_in_context_model(ctx, f1);

  yices_free_param_record(params);
  yices_free_context(ctx);
}

static void check_bitwise_sat_case(const char *delegate) {
  type_t bv8;
  term_t x, y, f0, f1;
  context_t *ctx;
  param_t *params;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);
  y = yices_new_uninterpreted_term(bv8);

  f0 = yices_bveq_atom(yices_bvand2(x, y), yices_bvconst_uint32(8, 0x0f));
  f1 = yices_bveq_atom(yices_bvor2(x, y), yices_bvconst_uint32(8, 0xff));

  ctx = new_qfbv_one_shot_context();
  assert(yices_assert_formula(ctx, f0) == 0);
  assert(yices_assert_formula(ctx, f1) == 0);

  params = new_delegate_params(delegate);
  expect_status(ctx, params, YICES_STATUS_SAT);
  assert_formula_true_in_context_model(ctx, f0);
  assert_formula_true_in_context_model(ctx, f1);

  yices_free_param_record(params);
  yices_free_context(ctx);
}

static void check_bitwise_unsat_not_case(const char *delegate) {
  type_t bv8;
  term_t x, f;
  context_t *ctx;
  param_t *params;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);
  f = yices_bveq_atom(x, yices_bvnot(x));

  ctx = new_qfbv_one_shot_context();
  assert(yices_assert_formula(ctx, f) == 0);

  params = new_delegate_params(delegate);
  expect_status(ctx, params, YICES_STATUS_UNSAT);

  yices_free_param_record(params);
  yices_free_context(ctx);
}

static void check_concat_extract_sat_case(const char *delegate) {
  type_t bv4;
  term_t hi, lo, z, f0, f1, f2, f3, f4;
  context_t *ctx;
  param_t *params;

  bv4 = yices_bv_type(4);
  hi = yices_new_uninterpreted_term(bv4);
  lo = yices_new_uninterpreted_term(bv4);
  z = yices_bvconcat2(hi, lo);

  f0 = yices_bveq_atom(hi, yices_bvconst_uint32(4, 0x0a));
  f1 = yices_bveq_atom(lo, yices_bvconst_uint32(4, 0x05));
  f2 = yices_bveq_atom(yices_bvextract(z, 4, 7), hi);
  f3 = yices_bveq_atom(yices_bvextract(z, 0, 3), lo);
  f4 = yices_bveq_atom(z, yices_bvconst_uint32(8, 0xa5));

  ctx = new_qfbv_one_shot_context();
  assert(yices_assert_formula(ctx, f0) == 0);
  assert(yices_assert_formula(ctx, f1) == 0);
  assert(yices_assert_formula(ctx, f2) == 0);
  assert(yices_assert_formula(ctx, f3) == 0);
  assert(yices_assert_formula(ctx, f4) == 0);

  params = new_delegate_params(delegate);
  expect_status(ctx, params, YICES_STATUS_SAT);
  assert_formula_true_in_context_model(ctx, f4);

  yices_free_param_record(params);
  yices_free_context(ctx);
}

static void check_add_self_unsat_case(const char *delegate) {
  type_t bv8;
  term_t x, f;
  context_t *ctx;
  param_t *params;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);
  f = yices_bveq_atom(yices_bvadd(x, yices_bvconst_uint32(8, 1)), x);

  ctx = new_qfbv_one_shot_context();
  assert(yices_assert_formula(ctx, f) == 0);

  params = new_delegate_params(delegate);
  expect_status(ctx, params, YICES_STATUS_UNSAT);

  yices_free_param_record(params);
  yices_free_context(ctx);
}

static void check_nested_pushpop_case(const char *delegate) {
  type_t bv8;
  term_t x, y, xeq0, xeq1, yeq1;
  context_t *ctx;
  param_t *params;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);
  y = yices_new_uninterpreted_term(bv8);
  xeq0 = yices_bveq_atom(x, yices_bvconst_uint32(8, 0));
  xeq1 = yices_bveq_atom(x, yices_bvconst_uint32(8, 1));
  yeq1 = yices_bveq_atom(y, yices_bvconst_uint32(8, 1));

  ctx = new_qfbv_pushpop_context();
  params = new_delegate_params(delegate);

  assert(yices_assert_formula(ctx, xeq0) == 0);
  expect_status(ctx, params, YICES_STATUS_SAT);

  assert(yices_push(ctx) == 0);
  assert(yices_assert_formula(ctx, yeq1) == 0);
  expect_status(ctx, params, YICES_STATUS_SAT);

  assert(yices_push(ctx) == 0);
  assert(yices_assert_formula(ctx, xeq1) == 0);
  expect_status(ctx, params, YICES_STATUS_UNSAT);

  assert(yices_pop(ctx) == 0);
  expect_status(ctx, params, YICES_STATUS_SAT);

  assert(yices_pop(ctx) == 0);
  expect_status(ctx, params, YICES_STATUS_SAT);

  yices_free_param_record(params);
  yices_free_context(ctx);
}

static void check_branching_pushpop_case(const char *delegate) {
  type_t bv8;
  term_t x, xeq0, xeq1, xneq0;
  context_t *ctx;
  param_t *params;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);
  xeq0 = yices_bveq_atom(x, yices_bvconst_uint32(8, 0));
  xeq1 = yices_bveq_atom(x, yices_bvconst_uint32(8, 1));
  xneq0 = yices_not(xeq0);

  ctx = new_qfbv_pushpop_context();
  params = new_delegate_params(delegate);

  assert(yices_assert_formula(ctx, xneq0) == 0);
  expect_status(ctx, params, YICES_STATUS_SAT);

  assert(yices_push(ctx) == 0);
  assert(yices_assert_formula(ctx, xeq0) == 0);
  expect_status(ctx, params, YICES_STATUS_UNSAT);
  assert(yices_pop(ctx) == 0);

  expect_status(ctx, params, YICES_STATUS_SAT);

  assert(yices_push(ctx) == 0);
  assert(yices_assert_formula(ctx, xeq1) == 0);
  expect_status(ctx, params, YICES_STATUS_SAT);
  assert(yices_pop(ctx) == 0);

  expect_status(ctx, params, YICES_STATUS_SAT);

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
      check_pushpop_incremental_case(delegates[i]);
      check_sat_model_value_case(delegates[i]);
      check_bitwise_sat_case(delegates[i]);
      check_bitwise_unsat_not_case(delegates[i]);
      check_concat_extract_sat_case(delegates[i]);
      check_add_self_unsat_case(delegates[i]);
      check_nested_pushpop_case(delegates[i]);
      check_branching_pushpop_case(delegates[i]);
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
