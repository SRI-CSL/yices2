/*
 * Regression test for issue #615:
 *
 * Yices used to crash with
 *   mcsat/value.c:478: mcsat_value_construct_from_value: Assertion `false' failed.
 * (or a SIGSEGV in release builds) when yices_check_context_with_model,
 * yices_check_context_with_model_and_hint, or yices_check_context_with_interpolation
 * was called with assumption variables whose type kind MCSAT cannot decide on
 * (e.g. uninterpreted, function, tuple, or finite-field types).
 *
 * The fix turns these crashes into a clean YICES_STATUS_ERROR with error code
 * MCSAT_ERROR_ASSUMPTION_TYPE_NOT_SUPPORTED.
 */

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include <yices.h>

static context_t *make_mcsat_context(bool model_interpolation) {
  ctx_config_t *config = yices_new_config();
  if (yices_set_config(config, "solver-type", "mcsat") < 0) goto error;
  if (model_interpolation &&
      yices_set_config(config, "model-interpolation", "true") < 0) goto error;

  context_t *ctx = yices_new_context(config);
  yices_free_config(config);
  return ctx;

 error:
  yices_print_error(stderr);
  yices_free_config(config);
  return NULL;
}

/*
 * Case 1: assumption variable of uninterpreted-sort type.
 * Reproduces the original crash trace from issue #615.
 */
static void check_uninterpreted_sort_assumption_rejected(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  type_t T = yices_new_uninterpreted_type();
  term_t x = yices_new_uninterpreted_term(T);
  term_t y = yices_new_uninterpreted_term(T);
  yices_set_term_name(x, "x_u");
  yices_set_term_name(y, "y_u");

  /* Make ctx satisfiable so the call really exercises mcsat. */
  yices_assert_formula(ctx, yices_neq(x, y));

  model_t *mdl = yices_new_model();
  term_t assumptions[2] = { x, y };

  smt_status_t s =
    yices_check_context_with_model(ctx, NULL, mdl, 2, assumptions);

  assert(s == YICES_STATUS_ERROR);
  assert(yices_error_code() == MCSAT_ERROR_ASSUMPTION_TYPE_NOT_SUPPORTED);
  yices_clear_error();

  s = yices_check_context_with_model_and_hint(ctx, NULL, mdl, 2,
                                              assumptions, /*m=*/1);
  assert(s == YICES_STATUS_ERROR);
  assert(yices_error_code() == MCSAT_ERROR_ASSUMPTION_TYPE_NOT_SUPPORTED);
  yices_clear_error();

  yices_free_model(mdl);
  yices_free_context(ctx);
}

/*
 * Case 2: assumption variable of function type.
 * Same crash path; same fix applies.
 */
static void check_function_type_assumption_rejected(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  type_t int_t = yices_int_type();
  type_t dom[1] = { int_t };
  type_t fty = yices_function_type(1, dom, int_t);
  term_t f = yices_new_uninterpreted_term(fty);
  yices_set_term_name(f, "f");

  yices_assert_formula(ctx, yices_eq(yices_application1(f, yices_int32(0)),
                                     yices_int32(0)));

  model_t *mdl = yices_new_model();
  term_t assumptions[1] = { f };

  smt_status_t s =
    yices_check_context_with_model(ctx, NULL, mdl, 1, assumptions);

  assert(s == YICES_STATUS_ERROR);
  assert(yices_error_code() == MCSAT_ERROR_ASSUMPTION_TYPE_NOT_SUPPORTED);
  yices_clear_error();

  yices_free_model(mdl);
  yices_free_context(ctx);
}

/*
 * Case 3: supported types must keep working unchanged.
 * Bool / Int / Real / BV / scalar assumptions go through the regular code path
 * and do not trigger the new error.
 */
static void check_supported_types_still_work(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  /* x : Real; assert x > 0; assumption x with model x = 1 -> SAT */
  term_t x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x_real");
  yices_assert_formula(ctx, yices_arith_gt0_atom(x));

  model_t *mdl = yices_new_model();
  yices_model_set_int32(mdl, x, 1);

  term_t assumptions[1] = { x };
  smt_status_t s =
    yices_check_context_with_model(ctx, NULL, mdl, 1, assumptions);
  /* Must not error and must not crash. */
  assert(s == YICES_STATUS_SAT || s == YICES_STATUS_UNKNOWN);

  yices_free_model(mdl);
  yices_free_context(ctx);
}

/*
 * Case 4: non-uninterpreted assumption term still reported with the original
 * MCSAT_ERROR_ASSUMPTION_TERM_NOT_SUPPORTED code (regression guard for
 * backward compatibility).
 */
static void check_term_shape_check_preserved(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  term_t x = yices_new_uninterpreted_term(yices_int_type());
  term_t not_a_var = yices_add(x, yices_int32(1));  /* x + 1, not a variable */

  model_t *mdl = yices_new_model();
  term_t assumptions[1] = { not_a_var };

  smt_status_t s =
    yices_check_context_with_model(ctx, NULL, mdl, 1, assumptions);
  assert(s == YICES_STATUS_ERROR);
  assert(yices_error_code() == MCSAT_ERROR_ASSUMPTION_TERM_NOT_SUPPORTED);
  yices_clear_error();

  yices_free_model(mdl);
  yices_free_context(ctx);
}

int main(void) {
  if (!yices_has_mcsat()) {
    return 1; /* skipped */
  }

  yices_init();

  check_uninterpreted_sort_assumption_rejected();
  check_function_type_assumption_rejected();
  check_supported_types_still_work();
  check_term_shape_check_preserved();

  yices_exit();
  printf("test_issue_615_assumption_type: PASS\n");
  return 0;
}
