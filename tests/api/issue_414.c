#include <stdbool.h>
#include <stdio.h>

#include "yices.h"

#define CHECK(COND, MSG) do { \
  if (!(COND)) { \
    fprintf(stderr, "issue_414: %s (line %d)\n", MSG, __LINE__); \
    yices_print_error(stderr); \
    return 2; \
  } \
} while (0)

static context_t *make_dpllt_context(void) {
  ctx_config_t *config;
  context_t *ctx;
  int32_t code;

  config = yices_new_config();
  code = yices_set_config(config, "solver-type", "dpllt");
  if (code < 0) goto error;
  ctx = yices_new_context(config);
  if (ctx == NULL) goto error;
  yices_free_config(config);
  return ctx;

 error:
  yices_print_error(stderr);
  yices_free_config(config);
  return NULL;
}

int main(void) {
  yices_init();

  /* Unit scalar type */
  type_t unit = yices_new_scalar_type(1);
  CHECK(unit != NULL_TYPE, "failed to create unit scalar type");

  term_t c0 = yices_constant(unit, 0);
  CHECK(c0 != NULL_TERM, "failed to create unit constant");

  /* Must create fresh uninterpreted terms even for unit type */
  term_t x = yices_new_uninterpreted_term(unit);
  term_t y = yices_new_uninterpreted_term(unit);
  CHECK(x != NULL_TERM && y != NULL_TERM, "failed to create unit uninterpreted terms");
  CHECK(x != y, "unit uninterpreted terms are not fresh");
  CHECK(yices_term_constructor(x) == YICES_UNINTERPRETED_TERM, "x is not uninterpreted");
  CHECK(yices_term_constructor(y) == YICES_UNINTERPRETED_TERM, "y is not uninterpreted");

  /* Substitution on unit terms must be accepted */
  {
    term_t var[1] = { x };
    term_t map[1] = { c0 };
    term_t r = yices_subst_term(1, var, map, x);
    CHECK(r == c0, "substitution on unit term failed");
    CHECK(yices_error_code() == 0, "unexpected error after substitution on unit term");
  }

  /* Model query on unit-typed uninterpreted term must succeed */
  {
    context_t *ctx = make_dpllt_context();
    CHECK(ctx != NULL, "failed to create dpllt context");

    CHECK(yices_assert_formula(ctx, yices_true()) == 0, "failed to assert true");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT, "expected SAT in empty context");

    model_t *mdl = yices_get_model(ctx, true);
    CHECK(mdl != NULL, "failed to build model");

    term_t v = yices_get_value_as_term(mdl, x);
    CHECK(v != NULL_TERM, "failed to query value for unit uninterpreted term");
    CHECK(yices_type_of_term(v) == unit, "model value for unit term has wrong type");

    yices_free_model(mdl);
    yices_free_context(ctx);
  }

  /* Singleton function type: Int -> unit */
  {
    type_t dom[1] = { yices_int_type() };
    type_t fun_unit = yices_function_type(1, dom, unit);
    CHECK(fun_unit != NULL_TYPE, "failed to create singleton function type");

    term_t f = yices_new_uninterpreted_term(fun_unit);
    term_t g = yices_new_uninterpreted_term(fun_unit);
    CHECK(f != NULL_TERM && g != NULL_TERM, "failed to create singleton-function terms");
    CHECK(f != g, "singleton-function uninterpreted terms are not fresh");
    CHECK(yices_term_constructor(f) == YICES_UNINTERPRETED_TERM, "f is not uninterpreted");
    CHECK(yices_term_constructor(g) == YICES_UNINTERPRETED_TERM, "g is not uninterpreted");

    /* Substitution must also accept singleton function terms */
    term_t var[1] = { f };
    term_t map[1] = { g };
    term_t r = yices_subst_term(1, var, map, f);
    CHECK(r == g, "substitution on singleton-function term failed");
    CHECK(yices_error_code() == 0, "unexpected error after substitution on function term");

    /* Since the function type is singleton, f != g must be UNSAT */
    context_t *ctx = make_dpllt_context();
    CHECK(ctx != NULL, "failed to create dpllt context for function test");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) == 0, "failed to assert f != g");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_UNSAT, "expected UNSAT for f != g on singleton type");
    yices_free_context(ctx);
  }

  yices_exit();
  return 0;
}
