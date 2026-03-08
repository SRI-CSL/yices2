#include <stdio.h>

#include "yices.h"

#define CHECK(COND, MSG) do { \
  if (!(COND)) { \
    fprintf(stderr, "issue_414_mcsat: %s (line %d)\n", MSG, __LINE__); \
    yices_print_error(stderr); \
    return 2; \
  } \
} while (0)

static context_t *make_mcsat_context(void) {
  ctx_config_t *config;
  context_t *ctx;

  config = yices_new_config();
  if (config == NULL) {
    return NULL;
  }

  if (yices_set_config(config, "solver-type", "mcsat") < 0) {
    yices_free_config(config);
    return NULL;
  }

  ctx = yices_new_context(config);
  yices_free_config(config);
  return ctx;
}

int main(void) {
  yices_init();

  if (!yices_has_mcsat()) {
    yices_exit();
    return 1; // skip
  }

  type_t unit = yices_new_scalar_type(1);
  CHECK(unit != NULL_TYPE, "failed to create scalar(1) type");

  // Case 1: singleton scalar constants x,y cannot be disequal.
  {
    term_t x = yices_new_uninterpreted_term(unit);
    term_t y = yices_new_uninterpreted_term(unit);
    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (const case)");
    CHECK(yices_assert_formula(ctx, yices_neq(x, y)) == 0, "failed to assert x != y");
    {
      smt_status_t st = yices_check_context(ctx, NULL);
      if (st != YICES_STATUS_UNSAT) {
        fprintf(stderr, "issue_414_mcsat: scalar case status=%d expected=%d\n",
                st, YICES_STATUS_UNSAT);
      }
      CHECK(st == YICES_STATUS_UNSAT, "expected UNSAT for x != y over scalar(1)");
    }
    yices_free_context(ctx);
  }

  // Case 2: finite function equality/disequality is rejected in MCSAT.
  {
    type_t dom[1] = { yices_int_type() };
    type_t fun_unit = yices_function_type(1, dom, unit);
    CHECK(fun_unit != NULL_TYPE, "failed to create (Int -> scalar(1)) type");

    term_t f = yices_new_uninterpreted_term(fun_unit);
    term_t g = yices_new_uninterpreted_term(fun_unit);
    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (function case)");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) < 0,
          "expected finite-function disequality to be rejected by MCSAT");
    CHECK(yices_error_code() == MCSAT_ERROR_UNSUPPORTED_THEORY,
          "expected MCSAT unsupported-theory error for finite-function disequality");
    yices_free_context(ctx);
  }

  // Case 3: same rejection for Bool -> Bool (finite domain and codomain).
  {
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bb = yices_function_type(1, dom, yices_bool_type());
    CHECK(fun_bb != NULL_TYPE, "failed to create (Bool -> Bool) type");

    term_t f = yices_new_uninterpreted_term(fun_bb);
    term_t g = yices_new_uninterpreted_term(fun_bb);
    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (Bool->Bool case)");
    CHECK(yices_assert_formula(ctx, yices_eq(f, g)) < 0,
          "expected finite-function equality to be rejected by MCSAT");
    CHECK(yices_error_code() == MCSAT_ERROR_UNSUPPORTED_THEORY,
          "expected MCSAT unsupported-theory error for finite-function equality");
    yices_free_context(ctx);
  }

  yices_exit();
  return 0;
}
