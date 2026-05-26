/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2026 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdbool.h>
#include <string.h>

/*
 * This test reaches into internal headers to inspect
 * sat_delegate_stats_t and context_get_sat_delegate_stats, which are
 * not exposed through the public yices.h API.  The corresponding
 * carve-out for -Wpedantic / -Wextra lives in tests/api/Makefile.
 */
#include "context/context.h"
#include "solvers/cdcl/delegate.h"
#include "yices.h"

static void expect_status(context_t *ctx, const param_t *params, smt_status_t expected) {
  smt_status_t stat;

  stat = yices_check_context(ctx, params);
  assert(stat == expected);
  assert(yices_error_code() == YICES_NO_ERROR);
}

static bool is_incremental_delegate_name(const char *delegate) {
  return strcmp(delegate, "cadical") == 0 || strcmp(delegate, "cryptominisat") == 0;
}

static bool supports_append_mode(const char *delegate) {
  return strcmp(delegate, "y2sat") == 0 || is_incremental_delegate_name(delegate);
}

static context_t *new_qfbv_pushpop_context_with_delegate(const char *delegate, const char *incremental_mode) {
  ctx_config_t *config;
  context_t *ctx;

  config = yices_new_config();
  assert(config != NULL);

  assert(yices_default_config_for_logic(config, "QF_BV") == 0);
  assert(yices_set_config(config, "mode", "push-pop") == 0);
  assert(yices_set_config(config, "sat-delegate", delegate) == 0);
  if (incremental_mode != NULL) {
    assert(yices_set_config(config, "sat-delegate-incremental-mode", incremental_mode) == 0);
  }

  ctx = yices_new_context(config);
  assert(ctx != NULL);

  yices_free_config(config);
  return ctx;
}

static term_t new_branching_sat_formula(void) {
  type_t bv8;
  term_t x, y, f0, f1;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);
  y = yices_new_uninterpreted_term(bv8);
  f0 = yices_bveq_atom(yices_bvand2(x, y), yices_bvconst_uint32(8, 0x0f));
  f1 = yices_bveq_atom(yices_bvor2(x, y), yices_bvconst_uint32(8, 0xff));

  return yices_and2(f0, f1);
}

static term_t new_bool_assumption(void) {
  return yices_new_uninterpreted_term(yices_bool_type());
}

static void check_default_mode_stats_case(const char *delegate) {
  term_t f;
  context_t *ctx;
  sat_delegate_stats_t stats;

  f = new_branching_sat_formula();

  ctx = new_qfbv_pushpop_context_with_delegate(delegate, NULL);
  assert(yices_assert_formula(ctx, f) == 0);
  expect_status(ctx, NULL, YICES_STATUS_SAT);

  context_get_sat_delegate_stats(ctx, &stats);
  if (strcmp(delegate, "y2sat") == 0) {
    assert(stats.append_checks == 1);
    assert(stats.rebuild_checks == 0);
    assert(stats.selector_frame_checks == 0);
  } else if (is_incremental_delegate_name(delegate)) {
    assert(stats.selector_frame_checks == 1);
    assert(stats.rebuild_checks == 0);
    assert(stats.append_checks == 0);
  } else {
    assert(stats.rebuild_checks == 1);
    assert(stats.append_checks == 0);
    assert(stats.selector_frame_checks == 0);
  }

  yices_free_context(ctx);
}

static void check_rebuild_mode_stats_case(const char *delegate) {
  term_t f0, f1;
  context_t *ctx;
  sat_delegate_stats_t stats;

  f0 = new_branching_sat_formula();
  f1 = new_branching_sat_formula();

  ctx = new_qfbv_pushpop_context_with_delegate(delegate, "rebuild");
  assert(yices_assert_formula(ctx, f0) == 0);
  expect_status(ctx, NULL, YICES_STATUS_SAT);
  assert(yices_assert_formula(ctx, f1) == 0);
  expect_status(ctx, NULL, YICES_STATUS_SAT);

  context_get_sat_delegate_stats(ctx, &stats);
  assert(stats.rebuild_checks == 2);
  assert(stats.append_checks == 0);
  assert(stats.selector_frame_checks == 0);

  yices_free_context(ctx);
}

static void check_append_mode_add_after_solve_case(const char *delegate) {
  term_t f0, f1;
  context_t *ctx;
  sat_delegate_stats_t stats;
  smt_status_t stat;
  term_t a;

  if (!supports_append_mode(delegate)) {
    return;
  }

  f0 = new_branching_sat_formula();
  f1 = new_branching_sat_formula();

  ctx = new_qfbv_pushpop_context_with_delegate(delegate, "append");
  assert(yices_assert_formula(ctx, f0) == 0);
  if (strcmp(delegate, "y2sat") == 0) {
    expect_status(ctx, NULL, YICES_STATUS_SAT);
  } else {
    a = new_bool_assumption();
    stat = yices_check_context_with_assumptions(ctx, NULL, 1, &a);
    assert(stat == YICES_STATUS_SAT);
  }
  assert(yices_assert_formula(ctx, f1) == 0);
  if (strcmp(delegate, "y2sat") == 0) {
    expect_status(ctx, NULL, YICES_STATUS_SAT);
  } else {
    stat = yices_check_context_with_assumptions(ctx, NULL, 1, &a);
    assert(stat == YICES_STATUS_SAT);
  }

  context_get_sat_delegate_stats(ctx, &stats);
  assert(stats.append_checks == 2);
  assert(stats.rebuild_checks == 0);
  assert(stats.selector_frame_checks == 0);
  if (strcmp(delegate, "y2sat") != 0) {
    assert(stats.delegate_initializations == 1);
    assert(stats.post_check_clause_forwards > 0);
  }

  yices_free_context(ctx);
}

static void check_y2sat_append_add_sat_clause_after_solve_case(void) {
  type_t bv8;
  term_t x, y, u, v, zero, a, b, p, d, hard, f0, f1;
  model_t *mdl;
  context_t *ctx;
  sat_delegate_stats_t stats;
  int32_t pval, dval;

  bv8 = yices_bv_type(8);
  x = yices_new_uninterpreted_term(bv8);
  y = yices_new_uninterpreted_term(bv8);
  u = yices_new_uninterpreted_term(bv8);
  v = yices_new_uninterpreted_term(bv8);
  zero = yices_bvconst_uint32(8, 0);
  a = yices_bveq_atom(yices_bvadd(x, yices_bvconst_uint32(8, 1)), x);
  b = yices_bveq_atom(y, zero);
  p = yices_bveq_atom(u, zero);
  d = yices_bveq_atom(v, zero);
  hard = yices_or2(a, b);
  f0 = yices_and2(hard, yices_or2(p, d));

  ctx = new_qfbv_pushpop_context_with_delegate("y2sat", "append");
  assert(yices_assert_formula(ctx, f0) == 0);
  expect_status(ctx, NULL, YICES_STATUS_SAT);

  mdl = yices_get_model(ctx, 1);
  assert(mdl != NULL);
  pval = yices_formula_true_in_model(mdl, p);
  assert(pval == 0 || pval == 1);
  dval = yices_formula_true_in_model(mdl, d);
  assert(dval == 0 || dval == 1);
  yices_free_model(mdl);

  f1 = yices_or2(pval ? yices_not(p) : p, dval ? yices_not(d) : d);

  assert(yices_assert_formula(ctx, f1) == 0);
  expect_status(ctx, NULL, YICES_STATUS_SAT);

  context_get_sat_delegate_stats(ctx, &stats);
  assert(stats.append_checks == 2);
  assert(stats.rebuild_checks == 0);

  yices_free_context(ctx);
}

static void check_y2sat_delegate_multi_check_add_clause_after_sat_case(void) {
  delegate_t delegate;
  literal_t clause[2];
  bval_t v1, v2;

  assert(init_delegate_incremental(&delegate, "y2sat", 3));

  clause[0] = pos_lit(1);
  clause[1] = pos_lit(2);
  delegate.add_clause(delegate.solver, 2, clause);
  assert(delegate.check(delegate.solver) == YICES_STATUS_SAT);

  v1 = delegate_get_value(&delegate, 1);
  v2 = delegate_get_value(&delegate, 2);
  assert(bval_is_def(v1));
  assert(bval_is_def(v2));

  clause[0] = (v1 == VAL_TRUE) ? neg_lit(1) : pos_lit(1);
  clause[1] = (v2 == VAL_TRUE) ? neg_lit(2) : pos_lit(2);
  delegate.add_clause(delegate.solver, 2, clause);
  assert(delegate.check(delegate.solver) == YICES_STATUS_SAT);

  delete_delegate(&delegate);
}

static void check_append_mode_rebuild_after_pop_case(const char *delegate) {
  term_t f0, f1;
  context_t *ctx;
  sat_delegate_stats_t stats;
  smt_status_t stat;
  term_t a;

  if (!supports_append_mode(delegate)) {
    return;
  }

  f0 = new_branching_sat_formula();
  f1 = new_branching_sat_formula();

  ctx = new_qfbv_pushpop_context_with_delegate(delegate, "append");
  assert(yices_assert_formula(ctx, f0) == 0);
  if (strcmp(delegate, "y2sat") == 0) {
    expect_status(ctx, NULL, YICES_STATUS_SAT);
  } else {
    a = new_bool_assumption();
    stat = yices_check_context_with_assumptions(ctx, NULL, 1, &a);
    assert(stat == YICES_STATUS_SAT);
  }
  assert(yices_push(ctx) == 0);
  assert(yices_assert_formula(ctx, f1) == 0);
  if (strcmp(delegate, "y2sat") == 0) {
    expect_status(ctx, NULL, YICES_STATUS_SAT);
  } else {
    stat = yices_check_context_with_assumptions(ctx, NULL, 1, &a);
    assert(stat == YICES_STATUS_SAT);
  }
  assert(yices_pop(ctx) == 0);
  if (strcmp(delegate, "y2sat") == 0) {
    expect_status(ctx, NULL, YICES_STATUS_SAT);
  } else {
    stat = yices_check_context_with_assumptions(ctx, NULL, 1, &a);
    assert(stat == YICES_STATUS_SAT);
  }

  context_get_sat_delegate_stats(ctx, &stats);
  assert(stats.append_checks == 3);
  if (strcmp(delegate, "y2sat") != 0) {
    assert(stats.delegate_initializations == 2);
    assert(stats.delegate_reinitializations == 1);
  }

  yices_free_context(ctx);
}

static void check_selector_mode_add_after_solve_case(const char *delegate) {
  term_t f0, f1;
  context_t *ctx;
  sat_delegate_stats_t stats;
  smt_status_t stat;
  term_t a;

  if (!is_incremental_delegate_name(delegate)) {
    return;
  }

  f0 = new_branching_sat_formula();
  f1 = new_branching_sat_formula();

  ctx = new_qfbv_pushpop_context_with_delegate(delegate, "selector-frames");
  assert(yices_push(ctx) == 0);
  assert(yices_assert_formula(ctx, f0) == 0);
  a = new_bool_assumption();
  stat = yices_check_context_with_assumptions(ctx, NULL, 1, &a);
  assert(stat == YICES_STATUS_SAT);
  assert(yices_assert_formula(ctx, f1) == 0);
  stat = yices_check_context_with_assumptions(ctx, NULL, 1, &a);
  assert(stat == YICES_STATUS_SAT);

  context_get_sat_delegate_stats(ctx, &stats);
  assert(stats.selector_frame_checks == 2);
  assert(stats.rebuild_checks == 0);
  assert(stats.append_checks == 0);
  assert(stats.selector_variables == 1);
  assert(stats.selector_assumptions == 2);
  assert(stats.post_check_clause_forwards > 0);

  yices_free_context(ctx);
}

static void check_selector_mode_long_pushpop_case(const char *delegate) {
  context_t *ctx;
  sat_delegate_stats_t stats;
  uint32_t i;

  if (!is_incremental_delegate_name(delegate)) {
    return;
  }

  ctx = new_qfbv_pushpop_context_with_delegate(delegate, "selector-frames");

  for (i=0; i<24; i++) {
    term_t f, a;
    smt_status_t stat;

    f = new_branching_sat_formula();
    a = new_bool_assumption();
    assert(yices_push(ctx) == 0);
    assert(yices_assert_formula(ctx, f) == 0);
    stat = yices_check_context_with_assumptions(ctx, NULL, 1, &a);
    assert(stat == YICES_STATUS_SAT);
    assert(yices_pop(ctx) == 0);
  }

  context_get_sat_delegate_stats(ctx, &stats);
  assert(stats.selector_variables == 24);
  assert(stats.selector_retirements == 24);
  assert(stats.selector_assumptions == 24);

  yices_free_context(ctx);
}

int main(void) {
  const char *delegates[] = { "y2sat", "cadical", "cryptominisat", "kissat" };
  uint32_t i;

  yices_init();
  assert(yices_has_delegate("y2sat"));

  for (i=0; i<sizeof(delegates)/sizeof(delegates[0]); i++) {
    if (yices_has_delegate(delegates[i])) {
      check_default_mode_stats_case(delegates[i]);
      check_rebuild_mode_stats_case(delegates[i]);
      check_append_mode_add_after_solve_case(delegates[i]);
      check_append_mode_rebuild_after_pop_case(delegates[i]);
      check_selector_mode_add_after_solve_case(delegates[i]);
      check_selector_mode_long_pushpop_case(delegates[i]);
    }
  }
  check_y2sat_append_add_sat_clause_after_solve_case();
  check_y2sat_delegate_multi_check_add_clause_after_sat_case();

  yices_exit();
  return 0;
}
