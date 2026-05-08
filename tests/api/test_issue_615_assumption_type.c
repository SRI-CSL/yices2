/*
 * Regression test for issue #615:
 *
 * Yices used to crash with
 *   mcsat/value.c:478: mcsat_value_construct_from_value: Assertion `false' failed.
 * (or a SIGSEGV in release builds) when yices_check_context_with_model,
 * yices_check_context_with_model_and_hint, or yices_check_context_with_interpolation
 * was called with assumption variables whose type kind MCSAT cannot decide on
 * (e.g. uninterpreted, function, or finite-field types). Tuple assumptions
 * whose flattened leaves are decidable scalar types are supported.
 *
 * The fix turns these crashes into a clean YICES_STATUS_ERROR with error code
 * MCSAT_ERROR_ASSUMPTION_TYPE_NOT_SUPPORTED.
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include <gmp.h>
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

static void set_tuple_int_bool(model_t *mdl, term_t tuple, int32_t i, int32_t b) {
  term_t ivar = yices_new_uninterpreted_term(yices_int_type());
  term_t bvar = yices_new_uninterpreted_term(yices_bool_type());
  yval_t elems[2];

  assert(yices_model_set_int32(mdl, ivar, i) == 0);
  assert(yices_model_set_bool(mdl, bvar, b) == 0);
  assert(yices_get_value(mdl, ivar, &elems[0]) == 0);
  assert(yices_get_value(mdl, bvar, &elems[1]) == 0);
  assert(yices_model_set_tuple(mdl, tuple, 2, elems) == 0);
}

static void set_tuple_int_scalar(model_t *mdl, term_t tuple, type_t scalar_t,
                                 int32_t i, int32_t s) {
  term_t ivar = yices_new_uninterpreted_term(yices_int_type());
  term_t svar = yices_new_uninterpreted_term(scalar_t);
  yval_t elems[2];

  assert(yices_model_set_int32(mdl, ivar, i) == 0);
  assert(yices_model_set_scalar(mdl, svar, s) == 0);
  assert(yices_get_value(mdl, ivar, &elems[0]) == 0);
  assert(yices_get_value(mdl, svar, &elems[1]) == 0);
  assert(yices_model_set_tuple(mdl, tuple, 2, elems) == 0);
}

static void set_nested_tuple_int_bool_bv(model_t *mdl, term_t tuple,
                                         int32_t i, int32_t b, uint32_t bv) {
  term_t ivar = yices_new_uninterpreted_term(yices_int_type());
  term_t bvar = yices_new_uninterpreted_term(yices_bool_type());
  term_t bvvar = yices_new_uninterpreted_term(yices_bv_type(4));
  yval_t outer[2], inner[2], inner_tuple;

  assert(yices_model_set_int32(mdl, ivar, i) == 0);
  assert(yices_model_set_bool(mdl, bvar, b) == 0);
  assert(yices_model_set_bv_uint32(mdl, bvvar, bv) == 0);
  assert(yices_get_value(mdl, ivar, &outer[0]) == 0);
  assert(yices_get_value(mdl, bvar, &inner[0]) == 0);
  assert(yices_get_value(mdl, bvvar, &inner[1]) == 0);
  assert(yices_model_make_tuple(mdl, 2, inner, &inner_tuple) == 0);
  outer[1] = inner_tuple;
  assert(yices_model_set_tuple(mdl, tuple, 2, outer) == 0);
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
  (void) s;

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
  (void) s;

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
  (void) s;
  /* Must not error and must not crash. */
  assert(s == YICES_STATUS_SAT || s == YICES_STATUS_UNKNOWN);

  yices_free_model(mdl);
  yices_free_context(ctx);

  ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  /* s : scalar(3); assert s = c1; assumption s with model s = c1 -> SAT */
  type_t scalar_t = yices_new_scalar_type(3);
  term_t s_var = yices_new_uninterpreted_term(scalar_t);
  term_t s_val = yices_constant(scalar_t, 1);
  yices_set_term_name(s_var, "x_scalar");
  assert(yices_assert_formula(ctx, yices_eq(s_var, s_val)) == 0);

  mdl = yices_new_model();
  assert(yices_model_set_scalar(mdl, s_var, 1) == 0);

  assumptions[0] = s_var;
  s = yices_check_context_with_model(ctx, NULL, mdl, 1, assumptions);
  assert(s == YICES_STATUS_SAT || s == YICES_STATUS_UNKNOWN);

  yices_free_model(mdl);
  yices_free_context(ctx);
}

static void check_tuple_assumption_sat(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  type_t tuple_t = yices_tuple_type2(yices_int_type(), yices_bool_type());
  term_t x = yices_new_uninterpreted_term(tuple_t);
  term_t assumptions[1] = { x };

  assert(yices_assert_formula(ctx, yices_arith_gt0_atom(yices_select(1, x))) == 0);
  assert(yices_assert_formula(ctx, yices_eq(yices_select(2, x), yices_true())) == 0);

  model_t *mdl = yices_new_model();
  set_tuple_int_bool(mdl, x, 3, 1);

  smt_status_t s = yices_check_context_with_model(ctx, NULL, mdl, 1, assumptions);
  assert(s == YICES_STATUS_SAT || s == YICES_STATUS_UNKNOWN);

  yices_free_model(mdl);
  yices_free_context(ctx);
}

static void check_tuple_assumption_unsat(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  type_t tuple_t = yices_tuple_type2(yices_int_type(), yices_bool_type());
  term_t x = yices_new_uninterpreted_term(tuple_t);
  term_t assumptions[1] = { x };

  assert(yices_assert_formula(ctx, yices_arith_gt0_atom(yices_select(1, x))) == 0);

  model_t *mdl = yices_new_model();
  set_tuple_int_bool(mdl, x, -1, 1);

  smt_status_t s = yices_check_context_with_model(ctx, NULL, mdl, 1, assumptions);
  assert(s == YICES_STATUS_UNSAT);

  yices_free_model(mdl);
  yices_free_context(ctx);
}

static void check_tuple_assumption_respects_preprocessing(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  type_t tuple_t = yices_tuple_type2(yices_int_type(), yices_bool_type());
  term_t x = yices_new_uninterpreted_term(tuple_t);
  term_t fixed = yices_tuple(2, (term_t[]){ yices_int32(2), yices_true() });
  term_t assumptions[1] = { x };

  assert(yices_assert_formula(ctx, yices_eq(x, fixed)) == 0);

  model_t *mdl = yices_new_model();
  set_tuple_int_bool(mdl, x, 3, 1);

  smt_status_t s = yices_check_context_with_model(ctx, NULL, mdl, 1, assumptions);
  assert(s == YICES_STATUS_UNSAT);

  yices_free_model(mdl);
  yices_free_context(ctx);
}

static void check_nested_tuple_assumption_sat(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  type_t bv4_t = yices_bv_type(4);
  type_t inner_t = yices_tuple_type2(yices_bool_type(), bv4_t);
  type_t outer_t = yices_tuple_type2(yices_int_type(), inner_t);
  term_t x = yices_new_uninterpreted_term(outer_t);
  term_t inner = yices_select(2, x);
  term_t assumptions[1] = { x };

  assert(yices_assert_formula(ctx, yices_arith_eq_atom(yices_select(1, x), yices_int32(5))) == 0);
  assert(yices_assert_formula(ctx, yices_eq(yices_select(1, inner), yices_false())) == 0);
  assert(yices_assert_formula(ctx, yices_bveq_atom(yices_select(2, inner),
                                                   yices_bvconst_uint32(4, 0xa))) == 0);

  model_t *mdl = yices_new_model();
  set_nested_tuple_int_bool_bv(mdl, x, 5, 0, 0xa);

  smt_status_t s = yices_check_context_with_model(ctx, NULL, mdl, 1, assumptions);
  assert(s == YICES_STATUS_SAT || s == YICES_STATUS_UNKNOWN);

  yices_free_model(mdl);
  yices_free_context(ctx);
}

static void check_tuple_with_scalar_leaf(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  type_t scalar_t = yices_new_scalar_type(3);
  type_t tuple_t = yices_tuple_type2(yices_int_type(), scalar_t);
  term_t x = yices_new_uninterpreted_term(tuple_t);
  term_t assumptions[1] = { x };

  assert(yices_assert_formula(ctx, yices_arith_eq_atom(yices_select(1, x), yices_int32(7))) == 0);
  assert(yices_assert_formula(ctx, yices_eq(yices_select(2, x),
                                            yices_constant(scalar_t, 2))) == 0);

  model_t *mdl = yices_new_model();
  set_tuple_int_scalar(mdl, x, scalar_t, 7, 2);

  smt_status_t s = yices_check_context_with_model(ctx, NULL, mdl, 1, assumptions);
  assert(s == YICES_STATUS_SAT || s == YICES_STATUS_UNKNOWN);

  yices_free_model(mdl);
  yices_free_context(ctx);
}

static void check_tuple_repeat_solve_resets_assumptions(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  type_t tuple_t = yices_tuple_type2(yices_int_type(), yices_bool_type());
  term_t x = yices_new_uninterpreted_term(tuple_t);
  term_t assumptions[1] = { x };

  assert(yices_assert_formula(ctx, yices_arith_gt0_atom(yices_select(1, x))) == 0);

  model_t *mdl = yices_new_model();
  set_tuple_int_bool(mdl, x, 4, 1);

  smt_status_t s = yices_check_context_with_model(ctx, NULL, mdl, 1, assumptions);
  assert(s == YICES_STATUS_SAT || s == YICES_STATUS_UNKNOWN);

  s = yices_check_context_with_model(ctx, NULL, mdl, 1, assumptions);
  assert(s == YICES_STATUS_SAT || s == YICES_STATUS_UNKNOWN);

  yices_free_model(mdl);
  yices_free_context(ctx);
}

static void check_tuple_model_hint(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  type_t tuple_t = yices_tuple_type2(yices_int_type(), yices_bool_type());
  term_t x = yices_new_uninterpreted_term(tuple_t);
  term_t y = yices_new_uninterpreted_term(tuple_t);
  term_t assumptions[2] = { x, y };

  assert(yices_assert_formula(ctx, yices_arith_eq_atom(yices_select(1, x), yices_int32(4))) == 0);

  model_t *mdl = yices_new_model();
  set_tuple_int_bool(mdl, x, 4, 1);
  set_tuple_int_bool(mdl, y, 9, 0);

  smt_status_t s = yices_check_context_with_model_and_hint(ctx, NULL, mdl, 2, assumptions, 1);
  assert(s == YICES_STATUS_SAT || s == YICES_STATUS_UNKNOWN);

  yices_free_model(mdl);
  yices_free_context(ctx);
}

static void check_tuple_interpolation_refutation(void) {
  context_t *ctx_A = make_mcsat_context(true);
  context_t *ctx_B = make_mcsat_context(false);
  assert(ctx_A != NULL && ctx_B != NULL);

  type_t tuple_t = yices_tuple_type2(yices_int_type(), yices_bool_type());
  term_t x = yices_new_uninterpreted_term(tuple_t);
  assert(yices_set_term_name(x, "issue615_tuple_interp_x") == 0);
  term_t a_tuple = yices_tuple(2, (term_t[]){ yices_int32(1), yices_true() });
  term_t b_tuple = yices_tuple(2, (term_t[]){ yices_int32(2), yices_true() });

  assert(yices_assert_formula(ctx_A, yices_eq(x, a_tuple)) == 0);
  assert(yices_assert_formula(ctx_B, yices_eq(x, b_tuple)) == 0);

  interpolation_context_t ictx = { ctx_A, ctx_B, NULL_TERM, NULL };
  smt_status_t s = yices_check_context_with_interpolation(&ictx, NULL, 0);
  assert(s == YICES_STATUS_UNSAT);
  assert(ictx.interpolant != NULL_TERM);

  yices_free_context(ctx_B);
  yices_free_context(ctx_A);
}

static void check_tuple_with_unsupported_leaf_rejected(void) {
  context_t *ctx = make_mcsat_context(false);
  assert(ctx != NULL);

  type_t int_t = yices_int_type();
  type_t u_t = yices_new_uninterpreted_type();
  type_t fun_t = yices_function_type1(int_t, int_t);
  mpz_t p;
  mpz_init_set_ui(p, 7);
  type_t ff_t = yices_ff_type(p);
  mpz_clear(p);

  type_t bad_types[3] = {
    yices_tuple_type2(int_t, u_t),
    yices_tuple_type2(int_t, fun_t),
    yices_tuple_type2(int_t, ff_t),
  };

  model_t *mdl = yices_new_model();
  for (uint32_t i = 0; i < 3; ++i) {
    term_t x = yices_new_uninterpreted_term(bad_types[i]);
    smt_status_t s = yices_check_context_with_model(ctx, NULL, mdl, 1, &x);
    assert(s == YICES_STATUS_ERROR);
    assert(yices_error_code() == MCSAT_ERROR_ASSUMPTION_TYPE_NOT_SUPPORTED);
    yices_clear_error();
  }

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
  (void) s;
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
  check_tuple_assumption_sat();
  check_tuple_assumption_unsat();
  check_tuple_assumption_respects_preprocessing();
  check_nested_tuple_assumption_sat();
  check_tuple_with_scalar_leaf();
  check_tuple_repeat_solve_resets_assumptions();
  check_tuple_model_hint();
  check_tuple_interpolation_refutation();
  check_tuple_with_unsupported_leaf_rejected();
  check_term_shape_check_preserved();

  yices_exit();
  printf("test_issue_615_assumption_type: PASS\n");
  return 0;
}
