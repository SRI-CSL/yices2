#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "yices.h"

#include "context/context_types.h"

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

static int64_t mcsat_stat_value(context_t *ctx, const char *name) {
  FILE *tmp;
  char line[256];
  char needle[160];
  int64_t value;

  if (ctx == NULL || ctx->mcsat == NULL) {
    return -1;
  }

  tmp = tmpfile();
  if (tmp == NULL) {
    return -1;
  }

  mcsat_show_stats(ctx->mcsat, tmp);
  fflush(tmp);
  rewind(tmp);

  snprintf(needle, sizeof(needle), ":%s ", name);
  value = -1;
  while (fgets(line, sizeof(line), tmp) != NULL) {
    char *p = strstr(line, needle);
    if (p != NULL) {
      value = strtoll(p + strlen(needle), NULL, 10);
      break;
    }
  }

  fclose(tmp);
  return value;
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

  // Case 9: higher-order ranges are accepted when their disequalities are covered recursively.
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
    CHECK(yices_assert_formula(ctx, yices_eq(f, g)) == 0,
          "failed to assert equality over a function range containing finite functions");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for equality over Int -> (Bool -> Int)");
    yices_free_context(ctx);
  }

  // Case 10: function-typed domains with infinite cardinality remain accepted.
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
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) == 0,
          "failed to assert disequality over a function-typed infinite domain");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for disequality over ((Bool -> Int) -> Int)");
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

  // Case 12: hitting the risky diff-witness cap must not stop the scanner
  // from recording a later non-risky explicit disequality.
  {
    type_t int_dom[1] = { yices_int_type() };
    type_t non_risky_fun = yices_function_type(1, int_dom, yices_bool_type());
    term_t f, g;
    context_t *ctx;
    int32_t i;

    CHECK(non_risky_fun != NULL_TYPE, "failed to create non-risky Int -> Bool type");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (cap-pressure case)");

    for (i = 0; i < 16; ++ i) {
      type_t risky_dom[1] = { yices_new_scalar_type(2 + i) };
      type_t risky_fun = yices_function_type(1, risky_dom, yices_int_type());
      term_t risky_f = yices_new_uninterpreted_term(risky_fun);
      term_t risky_g = yices_new_uninterpreted_term(risky_fun);
      CHECK(risky_dom[0] != NULL_TYPE && risky_fun != NULL_TYPE,
            "failed to create risky cap-pressure function type");
      CHECK(risky_f != NULL_TERM && risky_g != NULL_TERM,
            "failed to create risky function term");
      CHECK(yices_assert_formula(ctx, yices_neq(risky_f, risky_g)) == 0,
            "failed to assert risky cap-pressure disequality");
    }

    f = yices_new_uninterpreted_term(non_risky_fun);
    g = yices_new_uninterpreted_term(non_risky_fun);
    CHECK(f != NULL_TERM && g != NULL_TERM, "failed to create non-risky function terms");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) == 0,
          "failed to assert post-cap non-risky disequality");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for cap-pressure non-risky disequality");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_model") == 1,
          "post-cap non-risky disequality was not recorded");
    yices_free_context(ctx);
  }

  // Case 13: a post-cap unit-range function disequality is a direct conflict.
  {
    type_t int_dom[1] = { yices_int_type() };
    type_t unit_fun = yices_function_type(1, int_dom, unit);
    term_t f, g;
    context_t *ctx;
    int32_t i;

    CHECK(unit_fun != NULL_TYPE, "failed to create unit-range Int -> Unit type");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (unit cap-pressure case)");

    for (i = 0; i < 16; ++ i) {
      type_t risky_dom[1] = { yices_new_scalar_type(2 + i) };
      type_t risky_fun = yices_function_type(1, risky_dom, yices_int_type());
      term_t risky_f = yices_new_uninterpreted_term(risky_fun);
      term_t risky_g = yices_new_uninterpreted_term(risky_fun);
      CHECK(risky_dom[0] != NULL_TYPE && risky_fun != NULL_TYPE,
            "failed to create risky cap-pressure function type");
      CHECK(risky_f != NULL_TERM && risky_g != NULL_TERM,
            "failed to create risky function term");
      CHECK(yices_assert_formula(ctx, yices_neq(risky_f, risky_g)) == 0,
            "failed to assert risky cap-pressure disequality");
    }

    f = yices_new_uninterpreted_term(unit_fun);
    g = yices_new_uninterpreted_term(unit_fun);
    CHECK(f != NULL_TERM && g != NULL_TERM, "failed to create unit-range function terms");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) == 0,
          "failed to assert post-cap unit-range disequality");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_UNSAT,
          "expected UNSAT for post-cap unit-range disequality");
    yices_free_context(ctx);
  }

  // Case 14: a post-cap defined function disequality is still handled by
  // definitional reasoning, not silently dropped by the witness cap.
  {
    type_t int_dom[1] = { yices_int_type() };
    type_t non_risky_fun = yices_function_type(1, int_dom, yices_bool_type());
    term_t f, g, b, h;
    context_t *ctx;
    int32_t i;

    CHECK(non_risky_fun != NULL_TYPE, "failed to create non-risky Int -> Bool type");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (defined cap-pressure case)");

    for (i = 0; i < 16; ++ i) {
      type_t risky_dom[1] = { yices_new_scalar_type(2 + i) };
      type_t risky_fun = yices_function_type(1, risky_dom, yices_int_type());
      term_t risky_f = yices_new_uninterpreted_term(risky_fun);
      term_t risky_g = yices_new_uninterpreted_term(risky_fun);
      CHECK(risky_dom[0] != NULL_TYPE && risky_fun != NULL_TYPE,
            "failed to create risky cap-pressure function type");
      CHECK(risky_f != NULL_TERM && risky_g != NULL_TERM,
            "failed to create risky function term");
      CHECK(yices_assert_formula(ctx, yices_neq(risky_f, risky_g)) == 0,
            "failed to assert risky cap-pressure disequality");
    }

    f = yices_new_uninterpreted_term(non_risky_fun);
    g = yices_new_uninterpreted_term(non_risky_fun);
    b = yices_new_uninterpreted_term(yices_bool_type());
    h = yices_ite(b, f, g);
    CHECK(f != NULL_TERM && g != NULL_TERM && b != NULL_TERM && h != NULL_TERM,
          "failed to create function-typed ITE terms");
    CHECK(yices_assert_formula(ctx, b) == 0, "failed to assert ITE guard");
    CHECK(yices_assert_formula(ctx, yices_neq(h, f)) == 0,
          "failed to assert post-cap defined function disequality");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_UNSAT,
          "expected UNSAT for post-cap defined function disequality");
    yices_free_context(ctx);
  }

  // Case 15: higher-order constraints can separate risky function terms even
  // when f and g were not explicitly disequal.
  {
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bb = yices_function_type(1, dom, yices_bool_type());
    type_t pred_dom[1] = { fun_bb };
    type_t colors = yices_new_scalar_type(2);
    type_t pred_type = yices_function_type(1, pred_dom, colors);
    term_t p, f, g, p_f, p_g;
    context_t *ctx;

    CHECK(fun_bb != NULL_TYPE, "failed to create Bool -> Bool type (distinct-id risky case)");
    CHECK(colors != NULL_TYPE, "failed to create scalar(2) type (distinct-id risky case)");
    CHECK(pred_type != NULL_TYPE, "failed to create higher-order predicate type (distinct-id risky case)");

    p = yices_new_uninterpreted_term(pred_type);
    f = yices_new_uninterpreted_term(fun_bb);
    g = yices_new_uninterpreted_term(fun_bb);
    CHECK(p != NULL_TERM && f != NULL_TERM && g != NULL_TERM,
          "failed to create Bool -> Bool functions (distinct-id risky case)");

    p_f = yices_application1(p, f);
    p_g = yices_application1(p, g);
    CHECK(p_f != NULL_TERM && p_g != NULL_TERM,
          "failed to create Bool -> Bool applications (distinct-id risky case)");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (distinct-id risky case)");
    CHECK(yices_assert_formula(ctx, yices_eq(p_f, yices_constant(colors, 0))) == 0,
          "failed to assert p(f) color (distinct-id risky case)");
    CHECK(yices_assert_formula(ctx, yices_eq(p_g, yices_constant(colors, 1))) == 0,
          "failed to assert p(g) color (distinct-id risky case)");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for risky higher-order separation case");
    {
      model_t *model = yices_get_model(ctx, 1);
      CHECK(model != NULL, "failed to build model for risky higher-order separation case");
      CHECK(yices_formula_true_in_model(model, yices_neq(f, g)) == 1,
            "model must separate functions with different higher-order images");
      yices_free_model(model);
    }
    yices_free_context(ctx);
  }

  // Case 15b: diff witness terms are persistent for a function pair across
  // push/pop. Re-entering the same disequality may recreate the active scoped
  // obligation, but it must reuse the cached witness term.
  {
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bi = yices_function_type(1, dom, yices_int_type());
    term_t f, g, diseq;
    context_t *ctx;

    CHECK(fun_bi != NULL_TYPE, "failed to create Bool -> Int type (persistent witness case)");

    f = yices_new_uninterpreted_term(fun_bi);
    g = yices_new_uninterpreted_term(fun_bi);
    diseq = yices_neq(f, g);
    CHECK(f != NULL_TERM && g != NULL_TERM && diseq != NULL_TERM,
          "failed to create persistent witness disequality");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (persistent witness case)");

    CHECK(yices_push(ctx) == 0, "failed to push persistent witness context");
    CHECK(yices_assert_formula(ctx, diseq) == 0,
          "failed to assert first persistent witness disequality");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for first persistent witness disequality");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_witnesses") == 1,
          "first disequality did not allocate one witness");
    CHECK(yices_pop(ctx) == 0, "failed to pop persistent witness context");

    CHECK(yices_push(ctx) == 0, "failed to repush persistent witness context");
    CHECK(yices_assert_formula(ctx, diseq) == 0,
          "failed to assert second persistent witness disequality");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for second persistent witness disequality");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_witnesses") == 1,
          "same function pair allocated a second witness after pop");
    CHECK(yices_pop(ctx) == 0, "failed to pop second persistent witness context");

    yices_free_context(ctx);
  }

  // Case 16: distinct function ids on a non-risky equality-sensitive type are
  // enforced in the model without pairwise model records or UF diff witnesses.
  {
    type_t dom[1] = { yices_int_type() };
    type_t fun_ib = yices_function_type(1, dom, yices_bool_type());
    type_t pred_dom[1] = { fun_ib };
    type_t pred_type = yices_function_type(1, pred_dom, yices_bool_type());
    term_t p, f, g, p_f, p_g, f_0, g_0;
    context_t *ctx;

    CHECK(fun_ib != NULL_TYPE, "failed to create Int -> Bool type (distinct-id non-risky case)");
    CHECK(pred_type != NULL_TYPE, "failed to create higher-order predicate type (distinct-id non-risky case)");

    p = yices_new_uninterpreted_term(pred_type);
    f = yices_new_uninterpreted_term(fun_ib);
    g = yices_new_uninterpreted_term(fun_ib);
    CHECK(p != NULL_TERM && f != NULL_TERM && g != NULL_TERM,
          "failed to create Int -> Bool functions (distinct-id non-risky case)");

    p_f = yices_application1(p, f);
    p_g = yices_application1(p, g);
    f_0 = yices_application1(f, yices_int32(0));
    g_0 = yices_application1(g, yices_int32(0));
    CHECK(p_f != NULL_TERM && p_g != NULL_TERM && f_0 != NULL_TERM && g_0 != NULL_TERM,
          "failed to create Int -> Bool applications (distinct-id non-risky case)");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (distinct-id non-risky case)");
    CHECK(yices_assert_formula(ctx, p_f) == 0,
          "failed to assert p(f) (distinct-id non-risky case)");
    CHECK(yices_assert_formula(ctx, yices_not(p_g)) == 0,
          "failed to assert not p(g) (distinct-id non-risky case)");
    CHECK(yices_assert_formula(ctx, yices_not(f_0)) == 0,
          "failed to assert f(0) (distinct-id non-risky case)");
    CHECK(yices_assert_formula(ctx, yices_not(g_0)) == 0,
          "failed to assert g(0) (distinct-id non-risky case)");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for non-risky distinct-id model case");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_model") == 0,
          "non-risky distinct-id path enumerated model disequality pairs");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_witnesses") == 0,
          "non-risky distinct-id path allocated a UF diff witness");
    {
      model_t *model = yices_get_model(ctx, 1);
      CHECK(model != NULL, "failed to build model for non-risky distinct-id case");
      CHECK(yices_formula_true_in_model(model, yices_neq(f, g)) == 1,
            "model must satisfy non-risky distinct-id function disequality");
      yices_free_model(model);
    }
    yices_free_context(ctx);
  }

  // Case 16b: explicit non-risky disequality commitments are true in the model.
  {
    type_t dom[1] = { yices_int_type() };
    type_t fun_ib = yices_function_type(1, dom, yices_bool_type());
    term_t f, g;
    context_t *ctx;

    CHECK(fun_ib != NULL_TYPE, "failed to create Int -> Bool type (non-risky model case)");

    f = yices_new_uninterpreted_term(fun_ib);
    g = yices_new_uninterpreted_term(fun_ib);
    CHECK(f != NULL_TERM && g != NULL_TERM,
          "failed to create Int -> Bool functions (non-risky model case)");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (non-risky model case)");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) == 0,
          "failed to assert non-risky disequality");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for non-risky disequality");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_witnesses") == 0,
          "non-risky explicit disequality allocated a UF diff witness");
    {
      model_t *model = yices_get_model(ctx, 1);
      CHECK(model != NULL, "failed to build model for non-risky explicit disequality");
      CHECK(yices_formula_true_in_model(model, yices_neq(f, g)) == 1,
            "model must satisfy non-risky explicit function disequality");
      yices_free_model(model);
    }
    yices_free_context(ctx);
  }

  // Case 16c: multiple non-risky commitments over one type are all true in the model.
  {
    type_t dom[1] = { yices_int_type() };
    type_t fun_ib = yices_function_type(1, dom, yices_bool_type());
    term_t f, g, h, distinct;
    context_t *ctx;

    CHECK(fun_ib != NULL_TYPE, "failed to create Int -> Bool type (non-risky multi-model case)");

    f = yices_new_uninterpreted_term(fun_ib);
    g = yices_new_uninterpreted_term(fun_ib);
    h = yices_new_uninterpreted_term(fun_ib);
    {
      term_t funs[3] = { f, g, h };
      distinct = yices_distinct(3, funs);
    }
    CHECK(f != NULL_TERM && g != NULL_TERM && h != NULL_TERM && distinct != NULL_TERM,
          "failed to create non-risky distinct functions");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (non-risky multi-model case)");
    CHECK(yices_assert_formula(ctx, distinct) == 0,
          "failed to assert non-risky distinct term");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for multiple non-risky disequalities");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_witnesses") == 0,
          "non-risky distinct term allocated a UF diff witness");
    {
      model_t *model = yices_get_model(ctx, 1);
      CHECK(model != NULL, "failed to build model for multiple non-risky disequalities");
      CHECK(yices_formula_true_in_model(model, yices_neq(f, g)) == 1,
            "model must satisfy f != g");
      CHECK(yices_formula_true_in_model(model, yices_neq(f, h)) == 1,
            "model must satisfy f != h");
      CHECK(yices_formula_true_in_model(model, yices_neq(g, h)) == 1,
            "model must satisfy g != h");
      yices_free_model(model);
    }
    yices_free_context(ctx);
  }

  // Case 16d: model completion separates current classes, not just the
  // syntactic terms that originally appeared in a disequality.
  {
    type_t dom[1] = { yices_int_type() };
    type_t fun_ib = yices_function_type(1, dom, yices_bool_type());
    term_t f, g, h;
    context_t *ctx;

    CHECK(fun_ib != NULL_TYPE, "failed to create Int -> Bool type (non-risky merge-model case)");

    f = yices_new_uninterpreted_term(fun_ib);
    g = yices_new_uninterpreted_term(fun_ib);
    h = yices_new_uninterpreted_term(fun_ib);
    CHECK(f != NULL_TERM && g != NULL_TERM && h != NULL_TERM,
          "failed to create non-risky merge functions");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (non-risky merge-model case)");
    CHECK(yices_assert_formula(ctx, yices_eq(f, h)) == 0,
          "failed to assert non-risky equality");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) == 0,
          "failed to assert non-risky disequality after equality");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for non-risky equality plus disequality");
    {
      model_t *model = yices_get_model(ctx, 1);
      CHECK(model != NULL, "failed to build model for non-risky merge disequality");
      CHECK(yices_formula_true_in_model(model, yices_eq(f, h)) == 1,
            "model must preserve merged non-risky class");
      CHECK(yices_formula_true_in_model(model, yices_neq(h, g)) == 1,
            "model must separate merged class from disequal function");
      yices_free_model(model);
    }
    yices_free_context(ctx);
  }

  // Case 17: fresh ids on non-equality-sensitive function types remain
  // internal tags and do not create semantic disequality obligations.
  {
    type_t dom[1] = { yices_int_type() };
    type_t fun_ib = yices_function_type(1, dom, yices_bool_type());
    term_t f, g, f_0, g_0;
    context_t *ctx;

    CHECK(fun_ib != NULL_TYPE, "failed to create Int -> Bool type (non-sensitive id case)");

    f = yices_new_uninterpreted_term(fun_ib);
    g = yices_new_uninterpreted_term(fun_ib);
    CHECK(f != NULL_TERM && g != NULL_TERM,
          "failed to create Int -> Bool functions (non-sensitive id case)");

    f_0 = yices_application1(f, yices_int32(0));
    g_0 = yices_application1(g, yices_int32(0));
    CHECK(f_0 != NULL_TERM && g_0 != NULL_TERM,
          "failed to create Int -> Bool applications (non-sensitive id case)");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (non-sensitive id case)");
    CHECK(yices_assert_formula(ctx, yices_not(f_0)) == 0,
          "failed to assert f(0) (non-sensitive id case)");
    CHECK(yices_assert_formula(ctx, yices_not(g_0)) == 0,
          "failed to assert g(0) (non-sensitive id case)");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for non-sensitive id case");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_model") == 0,
          "non-sensitive function ids created a model disequality record");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_distinct_id") == 0,
          "non-sensitive function ids allocated distinct-id witnesses");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_witnesses") == 0,
          "non-sensitive function ids allocated UF diff witnesses");
    yices_free_context(ctx);
  }

  // Case 18: distinct function ids on a unit-range function type are a direct
  // conflict even when no explicit function disequality was asserted.
  {
    type_t dom[1] = { yices_int_type() };
    type_t fun_iu = yices_function_type(1, dom, unit);
    type_t pred_dom[1] = { fun_iu };
    type_t pred_type = yices_function_type(1, pred_dom, yices_bool_type());
    term_t p, f, g, p_f, p_g;
    context_t *ctx;

    CHECK(fun_iu != NULL_TYPE, "failed to create Int -> Unit type (distinct-id unit case)");
    CHECK(pred_type != NULL_TYPE, "failed to create predicate type (distinct-id unit case)");

    p = yices_new_uninterpreted_term(pred_type);
    f = yices_new_uninterpreted_term(fun_iu);
    g = yices_new_uninterpreted_term(fun_iu);
    CHECK(p != NULL_TERM && f != NULL_TERM && g != NULL_TERM,
          "failed to create Int -> Unit functions (distinct-id unit case)");

    p_f = yices_application1(p, f);
    p_g = yices_application1(p, g);
    CHECK(p_f != NULL_TERM && p_g != NULL_TERM,
          "failed to create higher-order unit applications (distinct-id unit case)");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (distinct-id unit case)");
    CHECK(yices_assert_formula(ctx, p_f) == 0,
          "failed to assert p(f) (distinct-id unit case)");
    CHECK(yices_assert_formula(ctx, yices_not(p_g)) == 0,
          "failed to assert not p(g) (distinct-id unit case)");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_UNSAT,
          "expected UNSAT for unit-range distinct-id case");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_witnesses") == 0,
          "unit-range distinct-id conflict allocated a UF diff witness");
    yices_free_context(ctx);
  }

  // Case 19: five semantic function ids cannot fit in the four Bool -> Bool
  // functions. This exercises the UF cardinality checker rather than relying
  // on term-level simplification of an explicit distinct term.
  {
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bb = yices_function_type(1, dom, yices_bool_type());
    type_t colors = yices_new_scalar_type(5);
    type_t pred_dom[1] = { fun_bb };
    type_t pred_type = yices_function_type(1, pred_dom, colors);
    term_t p;
    term_t funs[5];
    context_t *ctx;
    uint32_t i;

    CHECK(fun_bb != NULL_TYPE, "failed to create Bool -> Bool type (cardinality id case)");
    CHECK(colors != NULL_TYPE, "failed to create scalar(5) type (cardinality id case)");
    CHECK(pred_type != NULL_TYPE, "failed to create higher-order scalar map type (cardinality id case)");

    p = yices_new_uninterpreted_term(pred_type);
    CHECK(p != NULL_TERM, "failed to create higher-order scalar map (cardinality id case)");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (cardinality id case)");

    for (i = 0; i < 5; ++ i) {
      term_t app, color, eq;

      funs[i] = yices_new_uninterpreted_term(fun_bb);
      CHECK(funs[i] != NULL_TERM, "failed to create Bool -> Bool function (cardinality id case)");

      app = yices_application1(p, funs[i]);
      color = yices_constant(colors, i);
      eq = yices_eq(app, color);
      CHECK(app != NULL_TERM && color != NULL_TERM && eq != NULL_TERM,
            "failed to create higher-order scalar constraint (cardinality id case)");
      CHECK(yices_assert_formula(ctx, eq) == 0,
            "failed to assert higher-order scalar constraint (cardinality id case)");
    }

    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_UNSAT,
          "expected UNSAT for five semantic Bool -> Bool function ids");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_cardinality_conflicts") > 0,
          "semantic Bool -> Bool pigeonhole was not detected by cardinality");
    yices_free_context(ctx);
  }

  yices_exit();
  return 0;
}
