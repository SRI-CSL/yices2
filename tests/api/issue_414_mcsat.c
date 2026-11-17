/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "yices.h"

#include "context/context_types.h"
#include "model/models.h"

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

static bool function_value_has_exact_range_values(value_table_t *vtbl, value_t value, type_t fun_type);

static bool value_has_exact_function_type(value_table_t *vtbl, value_t value, type_t fun_type) {
  return value != null_value &&
    (object_is_function(vtbl, value) || object_is_update(vtbl, value)) &&
    vtbl_function_type(vtbl, value) == fun_type &&
    function_value_has_exact_range_values(vtbl, value, fun_type);
}

static bool function_range_value_has_type(value_table_t *vtbl, value_t value, type_t range_type) {
  if (type_kind(vtbl->type_table, range_type) == FUNCTION_TYPE) {
    return value_has_exact_function_type(vtbl, value, range_type);
  }

  return is_subtype(vtbl->type_table, vtbl_value_type(vtbl, value), range_type);
}

static bool function_map_result_has_type(value_table_t *vtbl, value_t map, type_t range_type) {
  return object_is_map(vtbl, map) &&
    function_range_value_has_type(vtbl, vtbl_map_result(vtbl, map), range_type);
}

static bool function_value_has_exact_range_values(value_table_t *vtbl, value_t value, type_t fun_type) {
  type_t range_type;
  uint32_t i;

  range_type = function_type_range(vtbl->type_table, fun_type);

  while (object_is_update(vtbl, value)) {
    value_update_t *update = vtbl_update(vtbl, value);
    if (!function_map_result_has_type(vtbl, update->map, range_type)) {
      return false;
    }
    value = update->fun;
  }

  if (!object_is_function(vtbl, value)) {
    return false;
  }

  value_fun_t *fun = vtbl_function(vtbl, value);
  if (fun->type != fun_type ||
      !function_range_value_has_type(vtbl, fun->def, range_type)) {
    return false;
  }

  for (i = 0; i < fun->map_size; ++ i) {
    if (!function_map_result_has_type(vtbl, fun->map[i], range_type)) {
      return false;
    }
  }

  return true;
}

static bool function_model_range_values_have_type(model_t *model, term_t f, type_t range_type) {
  value_t value = model_find_term_value(model, f);
  type_t fun_type = term_type(model->terms, f);

  return value_has_exact_function_type(model_get_vtbl(model), value, fun_type) &&
    function_type_range(model->terms->types, fun_type) == range_type;
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

  // Case 20: distinct-id diff witnesses are created for function-id class
  // representatives, not for every syntactic alias in those classes.
  {
    enum { NALIASES = 8 };
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bb = yices_function_type(1, dom, yices_bool_type());
    type_t colors = yices_new_scalar_type(2);
    type_t pred_dom[1] = { fun_bb };
    type_t pred_type = yices_function_type(1, pred_dom, colors);
    term_t p;
    term_t f[NALIASES];
    term_t g[NALIASES];
    context_t *ctx;
    uint32_t i;

    CHECK(fun_bb != NULL_TYPE, "failed to create Bool -> Bool type (representative case)");
    CHECK(colors != NULL_TYPE, "failed to create scalar(2) type (representative case)");
    CHECK(pred_type != NULL_TYPE, "failed to create higher-order predicate type (representative case)");

    p = yices_new_uninterpreted_term(pred_type);
    CHECK(p != NULL_TERM, "failed to create predicate term (representative case)");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (representative case)");

    for (i = 0; i < NALIASES; ++ i) {
      term_t p_f, p_g;

      f[i] = yices_new_uninterpreted_term(fun_bb);
      g[i] = yices_new_uninterpreted_term(fun_bb);
      CHECK(f[i] != NULL_TERM && g[i] != NULL_TERM,
            "failed to create alias functions (representative case)");

      if (i > 0) {
        CHECK(yices_assert_formula(ctx, yices_eq(f[0], f[i])) == 0,
              "failed to assert f alias equality (representative case)");
        CHECK(yices_assert_formula(ctx, yices_eq(g[0], g[i])) == 0,
              "failed to assert g alias equality (representative case)");
      }

      p_f = yices_application1(p, f[i]);
      p_g = yices_application1(p, g[i]);
      CHECK(p_f != NULL_TERM && p_g != NULL_TERM,
            "failed to create alias applications (representative case)");
      CHECK(yices_assert_formula(ctx, yices_eq(p_f, yices_constant(colors, 0))) == 0,
            "failed to assert f alias image (representative case)");
      CHECK(yices_assert_formula(ctx, yices_eq(p_g, yices_constant(colors, 1))) == 0,
            "failed to assert g alias image (representative case)");
    }

    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for representative distinct-id case");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_witnesses") == 1,
          "representative distinct-id path created redundant diff witnesses");
    yices_free_context(ctx);
  }

  // Case 21: compatible function types are keyed by max_super_type, so a
  // Bool -> Int function and a Bool -> Real function can reuse the same
  // function id when no constraint separates them.
  {
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bi = yices_function_type(1, dom, yices_int_type());
    type_t fun_br = yices_function_type(1, dom, yices_real_type());
    type_t pred_dom[1] = { fun_br };
    type_t pred_type = yices_function_type(1, pred_dom, yices_bool_type());
    term_t p, f, g, p_f, p_g;
    context_t *ctx;

    CHECK(fun_bi != NULL_TYPE, "failed to create Bool -> Int type (compatible key case)");
    CHECK(fun_br != NULL_TYPE, "failed to create Bool -> Real type (compatible key case)");
    CHECK(pred_type != NULL_TYPE, "failed to create predicate type (compatible key case)");

    p = yices_new_uninterpreted_term(pred_type);
    f = yices_new_uninterpreted_term(fun_bi);
    g = yices_new_uninterpreted_term(fun_br);
    CHECK(p != NULL_TERM && f != NULL_TERM && g != NULL_TERM,
          "failed to create compatible-key terms");

    p_f = yices_application1(p, f);
    p_g = yices_application1(p, g);
    CHECK(p_f != NULL_TERM && p_g != NULL_TERM,
          "failed to create compatible-key applications");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (compatible key case)");
    CHECK(yices_assert_formula(ctx, p_f) == 0,
          "failed to assert p(f) (compatible key case)");
    CHECK(yices_assert_formula(ctx, p_g) == 0,
          "failed to assert p(g) (compatible key case)");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for compatible function-id key case");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_distinct_id") == 0,
          "compatible equal functions produced a distinct-id obligation");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_witnesses") == 0,
          "compatible equal functions produced a diff witness");
    yices_free_context(ctx);
  }

  // Case 22: compatible shared-key model construction must not coerce a
  // narrower Bool -> Int view to a fractional Bool -> Real application value.
  {
    type_t dom[1] = { yices_bool_type() };
    type_t fun_bi = yices_function_type(1, dom, yices_int_type());
    type_t fun_br = yices_function_type(1, dom, yices_real_type());
    type_t pred_dom[1] = { fun_br };
    type_t pred_type = yices_function_type(1, pred_dom, yices_bool_type());
    term_t p, f, g, p_f, p_g, f_true, g_true, half;
    context_t *ctx;

    CHECK(fun_bi != NULL_TYPE, "failed to create Bool -> Int type (compatible model case)");
    CHECK(fun_br != NULL_TYPE, "failed to create Bool -> Real type (compatible model case)");
    CHECK(pred_type != NULL_TYPE, "failed to create predicate type (compatible model case)");

    p = yices_new_uninterpreted_term(pred_type);
    f = yices_new_uninterpreted_term(fun_bi);
    g = yices_new_uninterpreted_term(fun_br);
    half = yices_rational32(1, 2);
    CHECK(p != NULL_TERM && f != NULL_TERM && g != NULL_TERM && half != NULL_TERM,
          "failed to create compatible-model terms");

    p_f = yices_application1(p, f);
    p_g = yices_application1(p, g);
    f_true = yices_application1(f, yices_true());
    g_true = yices_application1(g, yices_true());
    CHECK(p_f != NULL_TERM && p_g != NULL_TERM && f_true != NULL_TERM && g_true != NULL_TERM,
          "failed to create compatible-model applications");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (compatible model case)");
    CHECK(yices_assert_formula(ctx, p_f) == 0,
          "failed to assert p(f) (compatible model case)");
    CHECK(yices_assert_formula(ctx, p_g) == 0,
          "failed to assert p(g) (compatible model case)");
    CHECK(yices_assert_formula(ctx, yices_arith_eq_atom(g_true, half)) == 0,
          "failed to assert g(true) = 1/2 (compatible model case)");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for compatible model case");
    {
      model_t *model = yices_get_model(ctx, 1);
      CHECK(model != NULL, "failed to build model for compatible model case");
      CHECK(yices_formula_true_in_model(model, yices_arith_eq_atom(g_true, half)) == 1,
            "model must preserve g(true) = 1/2");
      CHECK(yices_formula_true_in_model(model, yices_arith_neq_atom(f_true, half)) == 1,
            "model must keep Bool -> Int view away from fractional value");
      yices_free_model(model);
    }
    yices_free_context(ctx);
  }

  // Case 23: non-risky compatible function disequality model completion must
  // update each exact view with a value of that exact range, even when the
  // compatible supertype has a wider nested function range.
  {
    type_t bool_dom[1] = { yices_bool_type() };
    type_t int_dom[1] = { yices_int_type() };
    type_t inner_i = yices_function_type(1, bool_dom, yices_int_type());
    type_t inner_r = yices_function_type(1, bool_dom, yices_real_type());
    type_t outer_i = yices_function_type(1, int_dom, inner_i);
    type_t outer_r = yices_function_type(1, int_dom, inner_r);
    type_t colors = yices_new_scalar_type(2);
    type_t pred_dom[1] = { outer_r };
    type_t pred_type = yices_function_type(1, pred_dom, colors);
    term_t p, f, g, p_f, p_g;
    context_t *ctx;

    CHECK(inner_i != NULL_TYPE && inner_r != NULL_TYPE,
          "failed to create nested inner function types (non-risky model case)");
    CHECK(outer_i != NULL_TYPE && outer_r != NULL_TYPE,
          "failed to create nested outer function types (non-risky model case)");
    CHECK(pred_type != NULL_TYPE,
          "failed to create nested predicate type (non-risky model case)");

    p = yices_new_uninterpreted_term(pred_type);
    f = yices_new_uninterpreted_term(outer_i);
    g = yices_new_uninterpreted_term(outer_r);
    CHECK(p != NULL_TERM && f != NULL_TERM && g != NULL_TERM,
          "failed to create nested model terms");

    p_f = yices_application1(p, f);
    p_g = yices_application1(p, g);
    CHECK(p_f != NULL_TERM && p_g != NULL_TERM,
          "failed to create nested model applications");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (non-risky nested model case)");
    CHECK(yices_assert_formula(ctx, yices_eq(p_f, yices_constant(colors, 0))) == 0,
          "failed to assert p(f) image (non-risky nested model case)");
    CHECK(yices_assert_formula(ctx, yices_eq(p_g, yices_constant(colors, 1))) == 0,
          "failed to assert p(g) image (non-risky nested model case)");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) == 0,
          "failed to assert f != g (non-risky nested model case)");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for non-risky nested model case");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_model") == 1,
          "nested non-risky case should use model disequality completion");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_witnesses") == 0,
          "nested non-risky case should not create search diff witnesses");
    {
      model_t *model = yices_get_model(ctx, 1);
      CHECK(model != NULL, "failed to build model for non-risky nested model case");
      CHECK(function_model_range_values_have_type(model, f, inner_i),
            "nested non-risky model must keep f range values at Bool -> Int");
      CHECK(function_model_range_values_have_type(model, g, inner_r),
            "nested non-risky model must keep g range values at Bool -> Real");
      yices_free_model(model);
    }
    yices_free_context(ctx);
  }

  // Case 24: risky compatible function disequality witnesses must also update
  // each exact view with a value of that exact nested function range.
  {
    type_t bool_dom[1] = { yices_bool_type() };
    type_t inner_i = yices_function_type(1, bool_dom, yices_int_type());
    type_t inner_r = yices_function_type(1, bool_dom, yices_real_type());
    type_t outer_i = yices_function_type(1, bool_dom, inner_i);
    type_t outer_r = yices_function_type(1, bool_dom, inner_r);
    type_t colors = yices_new_scalar_type(2);
    type_t pred_dom[1] = { outer_r };
    type_t pred_type = yices_function_type(1, pred_dom, colors);
    term_t p, f, g, p_f, p_g;
    context_t *ctx;

    CHECK(inner_i != NULL_TYPE && inner_r != NULL_TYPE,
          "failed to create nested inner function types (risky witness case)");
    CHECK(outer_i != NULL_TYPE && outer_r != NULL_TYPE,
          "failed to create nested outer function types (risky witness case)");
    CHECK(pred_type != NULL_TYPE,
          "failed to create nested predicate type (risky witness case)");

    p = yices_new_uninterpreted_term(pred_type);
    f = yices_new_uninterpreted_term(outer_i);
    g = yices_new_uninterpreted_term(outer_r);
    CHECK(p != NULL_TERM && f != NULL_TERM && g != NULL_TERM,
          "failed to create nested witness terms");

    p_f = yices_application1(p, f);
    p_g = yices_application1(p, g);
    CHECK(p_f != NULL_TERM && p_g != NULL_TERM,
          "failed to create nested witness applications");

    ctx = make_mcsat_context();
    CHECK(ctx != NULL, "failed to create mcsat context (risky nested witness case)");
    CHECK(yices_assert_formula(ctx, yices_eq(p_f, yices_constant(colors, 0))) == 0,
          "failed to assert p(f) image (risky nested witness case)");
    CHECK(yices_assert_formula(ctx, yices_eq(p_g, yices_constant(colors, 1))) == 0,
          "failed to assert p(g) image (risky nested witness case)");
    CHECK(yices_assert_formula(ctx, yices_neq(f, g)) == 0,
          "failed to assert f != g (risky nested witness case)");
    CHECK(yices_check_context(ctx, NULL) == YICES_STATUS_SAT,
          "expected SAT for risky nested witness case");
    CHECK(mcsat_stat_value(ctx, "mcsat::uf::fun_diseq_witnesses") > 0,
          "nested risky case should create diff witnesses");
    {
      model_t *model = yices_get_model(ctx, 1);
      CHECK(model != NULL, "failed to build model for risky nested witness case");
      CHECK(function_model_range_values_have_type(model, f, inner_i),
            "nested risky witness model must keep f range values at Bool -> Int");
      CHECK(function_model_range_values_have_type(model, g, inner_r),
            "nested risky witness model must keep g range values at Bool -> Real");
      yices_free_model(model);
    }
    yices_free_context(ctx);
  }

  yices_exit();
  return 0;
}
