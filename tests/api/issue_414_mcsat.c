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

  // Case 2: singleton-range function disequality is unsatisfiable.
  {
    type_t dom[1] = { yices_int_type() };
    type_t fun_unit = yices_function_type(1, dom, unit);
    CHECK(fun_unit != NULL_TYPE, "failed to create (Int -> scalar(1)) type");

    term_t f = yices_new_uninterpreted_term(fun_unit);
    term_t g = yices_new_uninterpreted_term(fun_unit);
    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (function case)");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) == 0,
          "failed to assert singleton-range function disequality");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_UNSAT,
          "expected UNSAT for disequality over Int -> scalar(1)");
    yices_free_context(ctx);
  }

  // Case 3: Bool -> Bool function equality is satisfiable.
  {
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bb = yices_function_type(1, dom, yices_bool_type());
    CHECK(fun_bb != NULL_TYPE, "failed to create (Bool -> Bool) type");

    term_t f = yices_new_uninterpreted_term(fun_bb);
    term_t g = yices_new_uninterpreted_term(fun_bb);
    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (Bool->Bool case)");
    CHECK(yices_assert_formula(ctx, yices_eq(f, g)) == 0,
          "failed to assert Bool -> Bool function equality");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for equality over Bool -> Bool");
    yices_free_context(ctx);
  }

  // Case 4: three Bool -> Bool functions can be pairwise distinct.
  {
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bb = yices_function_type(1, dom, yices_bool_type());
    CHECK(fun_bb != NULL_TYPE, "failed to create (Bool -> Bool) type");

    term_t funs[3] = {
      yices_new_uninterpreted_term(fun_bb),
      yices_new_uninterpreted_term(fun_bb),
      yices_new_uninterpreted_term(fun_bb),
    };
    term_t distinct = yices_distinct(3, funs);
    CHECK(distinct != NULL_TERM, "failed to create distinct finite-function term");

    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (distinct Bool->Bool case)");
    CHECK(yices_assert_formula(ctx, distinct) == 0,
          "failed to assert distinct Bool -> Bool functions");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for three distinct Bool -> Bool functions");
    yices_free_context(ctx);
  }

  // Case 5: five Bool -> Bool functions cannot be pairwise distinct.
  {
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bb = yices_function_type(1, dom, yices_bool_type());
    CHECK(fun_bb != NULL_TYPE, "failed to create (Bool -> Bool) type");

    term_t funs[5] = {
      yices_new_uninterpreted_term(fun_bb),
      yices_new_uninterpreted_term(fun_bb),
      yices_new_uninterpreted_term(fun_bb),
      yices_new_uninterpreted_term(fun_bb),
      yices_new_uninterpreted_term(fun_bb),
    };
    term_t distinct = yices_distinct(5, funs);
    CHECK(distinct != NULL_TERM, "failed to create pigeonhole distinct term");

    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (pigeonhole Bool->Bool case)");
    CHECK(yices_assert_formula(ctx, distinct) == 0,
          "failed to assert five distinct Bool -> Bool functions");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_UNSAT,
          "expected UNSAT for five distinct Bool -> Bool functions");
    yices_free_context(ctx);
  }

  // Case 6: finite-domain functions with infinite codomain can be disequal.
  {
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bi = yices_function_type(1, dom, yices_int_type());
    CHECK(fun_bi != NULL_TYPE, "failed to create (Bool -> Int) type");

    term_t f = yices_new_uninterpreted_term(fun_bi);
    term_t g = yices_new_uninterpreted_term(fun_bi);
    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (Bool->Int case)");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) == 0,
          "failed to assert Bool -> Int function disequality");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for disequality over Bool -> Int");
    {
      model_t *model = yices_get_model(ctx, 1);
      term_t diff = yices_get_term_by_name("mcsat_diff_0_0");
      term_t f_diff, g_diff;
      int32_t diff_value;

      CHECK(model != NULL, "failed to build model for Bool -> Int disequality");
      CHECK(diff != NULL_TERM, "failed to retrieve generated diff witness");
      CHECK(yices_get_bool_value(model, diff, &diff_value) == 0,
            "model must define generated diff witness");

      f_diff = yices_application1(f, diff);
      g_diff = yices_application1(g, diff);
      CHECK(f_diff != NULL_TERM && g_diff != NULL_TERM,
            "failed to rebuild witness applications");
      CHECK(yices_formula_true_in_model(model, yices_neq(f_diff, g_diff)) == 1,
            "model must satisfy witness applications disequality");
      yices_free_model(model);
    }
    yices_free_context(ctx);
  }

  // Case 7: DISTINCT_TERM over Bool -> Int functions is satisfiable.
  {
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bi = yices_function_type(1, dom, yices_int_type());
    CHECK(fun_bi != NULL_TYPE, "failed to create (Bool -> Int) type");

    term_t funs[3] = {
      yices_new_uninterpreted_term(fun_bi),
      yices_new_uninterpreted_term(fun_bi),
      yices_new_uninterpreted_term(fun_bi),
    };
    term_t distinct = yices_distinct(3, funs);
    CHECK(distinct != NULL_TERM, "failed to create distinct finite-domain function term");

    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (distinct Bool->Int case)");
    CHECK(yices_assert_formula(ctx, distinct) == 0,
          "failed to assert distinct Bool -> Int functions");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for three distinct Bool -> Int functions");
    yices_free_context(ctx);
  }

  // Case 8: n-ary writes use all index components in read-over-write.
  {
    type_t dom[2] = { yices_bool_type(), yices_bool_type() };
    type_t fun_bbi = yices_function_type(2, dom, yices_int_type());
    CHECK(fun_bbi != NULL_TYPE, "failed to create (Bool Bool -> Int) type");

    term_t f = yices_new_uninterpreted_term(fun_bbi);
    term_t update = yices_update2(f, yices_false(), yices_true(), yices_int32(0));
    term_t update_read = yices_application2(update, yices_false(), yices_false());
    term_t base_read = yices_application2(f, yices_false(), yices_false());
    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (n-ary update case)");
    CHECK(update != NULL_TERM && update_read != NULL_TERM && base_read != NULL_TERM,
          "failed to create n-ary update/read terms");
    CHECK(yices_assert_formula(ctx, yices_neq(update_read, base_read)) == 0,
          "failed to assert n-ary read-over-write contradiction");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_UNSAT,
          "expected UNSAT for n-ary read-over-write contradiction");
    yices_free_context(ctx);
  }

  // Case 9: the guard is downward-closed through function ranges.
  {
    type_t bool_dom[1] = { yices_bool_type() };
    type_t int_dom[1] = { yices_int_type() };
    type_t fun_bi = yices_function_type(1, bool_dom, yices_int_type());
    type_t higher_order = yices_function_type(1, int_dom, fun_bi);
    CHECK(fun_bi != NULL_TYPE, "failed to create (Bool -> Int) type");
    CHECK(higher_order != NULL_TYPE, "failed to create (Int -> (Bool -> Int)) type");

    term_t f = yices_new_uninterpreted_term(higher_order);
    term_t g = yices_new_uninterpreted_term(higher_order);
    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (range closure case)");
    CHECK(yices_assert_formula(ctx, yices_eq(f, g)) < 0,
          "expected equality over a function range containing finite functions to be rejected");
    CHECK(yices_error_code() == MCSAT_ERROR_UNSUPPORTED_THEORY,
          "expected MCSAT unsupported-theory error for range closure");
    yices_free_context(ctx);
  }

  // Case 10: the guard is downward-closed through function domains.
  {
    type_t bool_dom[1] = { yices_bool_type() };
    type_t fun_bi = yices_function_type(1, bool_dom, yices_int_type());
    type_t fun_dom[1] = { fun_bi };
    type_t higher_order = yices_function_type(1, fun_dom, yices_int_type());
    CHECK(fun_bi != NULL_TYPE, "failed to create (Bool -> Int) type");
    CHECK(higher_order != NULL_TYPE, "failed to create ((Bool -> Int) -> Int) type");

    term_t f = yices_new_uninterpreted_term(higher_order);
    term_t g = yices_new_uninterpreted_term(higher_order);
    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (domain closure case)");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) < 0,
          "expected disequality over a function domain containing finite functions to be rejected");
    CHECK(yices_error_code() == MCSAT_ERROR_UNSUPPORTED_THEORY,
          "expected MCSAT unsupported-theory error for domain closure");
    yices_free_context(ctx);
  }

  // Case 11: infinite-domain, non-unit-codomain function disequality remains accepted.
  {
    type_t dom[1] = { yices_int_type() };
    type_t fun_ib = yices_function_type(1, dom, yices_bool_type());
    CHECK(fun_ib != NULL_TYPE, "failed to create (Int -> Bool) type");

    term_t f = yices_new_uninterpreted_term(fun_ib);
    term_t g = yices_new_uninterpreted_term(fun_ib);
    context_t *ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (Int->Bool case)");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) == 0,
          "expected infinite-domain non-unit function disequality to be accepted by MCSAT");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for disequality over Int -> Bool");
    yices_free_context(ctx);
  }

  yices_exit();
  return 0;
}
