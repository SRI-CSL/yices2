/*
 * Issue #680: model after a SAT check with assumptions in an MCSAT context.
 */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <yices.h>

static void fail(const char *msg) {
  fprintf(stderr, "%s\n", msg);
  exit(2);
}

/*
 * With no logic, solver-type mcsat runs in the push/pop mode (the reporter's setup).
 * A context without push/pop needs a logic and the multi-checks mode.
 */
static context_t *make_mcsat_context(bool pushpop) {
  ctx_config_t *config;
  context_t *context;

  config = yices_new_config();
  if ((!pushpop && (yices_default_config_for_logic(config, "QF_NRA") < 0 ||
                    yices_set_config(config, "mode", "multi-checks") < 0)) ||
      yices_set_config(config, "solver-type", "mcsat") < 0) {
    yices_print_error(stderr);
    fail("failed to configure mcsat context");
  }
  context = yices_new_context(config);
  yices_free_config(config);
  if (context == NULL) {
    yices_print_error(stderr);
    fail("failed to create mcsat context");
  }
  return context;
}

static void assert_formula(context_t *ctx, term_t f) {
  if (yices_assert_formula(ctx, f) < 0) {
    yices_print_error(stderr);
    fail("yices_assert_formula failed");
  }
}

static void check_assuming(context_t *ctx, uint32_t n, const term_t a[], smt_status_t expected) {
  if (yices_check_context_with_assumptions(ctx, NULL, n, a) != expected) {
    yices_print_error(stderr);
    fail("unexpected status from yices_check_context_with_assumptions");
  }
}

static void check_assuming_sat(context_t *ctx, uint32_t n, const term_t a[]) {
  check_assuming(ctx, n, a, YICES_STATUS_SAT);
}

static model_t *get_model(context_t *ctx) {
  model_t *mdl;

  mdl = yices_get_model(ctx, 0);
  if (mdl == NULL) {
    yices_print_error(stderr);
    fail("yices_get_model failed after a SAT check with assumptions");
  }
  return mdl;
}

static void expect_true(model_t *mdl, term_t f, const char *msg) {
  if (yices_formula_true_in_model(mdl, f) != 1) {
    fail(msg);
  }
}

static void expect_model_true(context_t *ctx, term_t f, const char *msg) {
  model_t *mdl;

  mdl = get_model(ctx);
  expect_true(mdl, f, msg);
  yices_free_model(mdl);
}

static void expect_core_is(context_t *ctx, term_t a, const char *msg) {
  term_vector_t core;

  yices_init_term_vector(&core);
  if (yices_get_unsat_core(ctx, &core) < 0 || core.size != 1 || core.data[0] != a) {
    fail(msg);
  }
  yices_delete_term_vector(&core);
}

/*
 * The reporter's example: (xor a b) with assumptions a and c.
 */
static void test_model_after_sat_assumptions(void) {
  context_t *ctx;
  type_t bool_ty;
  term_t a, b, c, xor_ab;
  term_t assumptions[2];
  model_t *mdl;

  ctx = make_mcsat_context(true);
  bool_ty = yices_bool_type();
  a = yices_new_uninterpreted_term(bool_ty);
  b = yices_new_uninterpreted_term(bool_ty);
  c = yices_new_uninterpreted_term(bool_ty);
  xor_ab = yices_xor2(a, b);
  assert_formula(ctx, xor_ab);

  assumptions[0] = a;
  assumptions[1] = c;
  check_assuming_sat(ctx, 2, assumptions);

  // When an MCSAT check with assumptions returns sat, `yices_context_status` shall return
  // `YICES_STATUS_SAT` for that context.
  if (yices_context_status(ctx) != YICES_STATUS_SAT) {
    fail("context status is not SAT after a SAT check with assumptions");
  }

  // While an MCSAT context has the status sat from an MCSAT check with assumptions,
  // `yices_get_model` shall return a model that gives true to each assertion and to each
  // assumption.
  mdl = get_model(ctx);
  expect_true(mdl, xor_ab, "model does not satisfy (xor a b)");
  expect_true(mdl, a, "model does not satisfy assumption a");
  expect_true(mdl, c, "model does not satisfy assumption c");
  yices_free_model(mdl);

  yices_free_context(ctx);
}

/*
 * Assumptions that are not Boolean variables: (> x 2) and (< x 3), with (< x 5) asserted.
 */
static void test_model_after_sat_arith_assumptions(void) {
  context_t *ctx;
  term_t x, lt5, gt2, lt3;
  term_t assumptions[2];
  model_t *mdl;

  ctx = make_mcsat_context(true);
  x = yices_new_uninterpreted_term(yices_real_type());
  lt5 = yices_arith_lt_atom(x, yices_int32(5));
  gt2 = yices_arith_gt_atom(x, yices_int32(2));
  lt3 = yices_arith_lt_atom(x, yices_int32(3));
  assert_formula(ctx, lt5);

  assumptions[0] = gt2;
  assumptions[1] = lt3;
  check_assuming_sat(ctx, 2, assumptions);

  // While an MCSAT context has the status sat from an MCSAT check with assumptions,
  // `yices_get_model` shall return a model that gives true to each assertion and to each
  // assumption.
  mdl = get_model(ctx);
  expect_true(mdl, lt5, "model does not satisfy (< x 5)");
  expect_true(mdl, gt2, "model does not satisfy assumption (> x 2)");
  expect_true(mdl, lt3, "model does not satisfy assumption (< x 3)");
  yices_free_model(mdl);

  yices_free_context(ctx);
}

static void push(context_t *ctx) {
  if (yices_push(ctx) < 0) {
    yices_print_error(stderr);
    fail("yices_push failed");
  }
}

static void pop(context_t *ctx) {
  if (yices_pop(ctx) < 0) {
    yices_print_error(stderr);
    fail("yices_pop of the user scope failed");
  }
}

static void pop_one_scope_only(context_t *ctx) {
  pop(ctx);
  if (yices_pop(ctx) >= 0) {
    fail("yices_pop succeeded with no user scope left");
  }
}

static void test_pop_without_user_scope_after_sat_assumptions(void) {
  context_t *ctx;
  term_t a;

  ctx = make_mcsat_context(true);
  a = yices_new_uninterpreted_term(yices_bool_type());
  check_assuming_sat(ctx, 1, &a);

  // Where an MCSAT context supports push and pop, while the context has no user scope and has
  // the status sat from an MCSAT check with assumptions, if `yices_pop` is called, then
  // `yices_pop` shall return -1 with the error code `CTX_INVALID_OPERATION`.
  if (yices_pop(ctx) >= 0) {
    fail("yices_pop succeeded with no user scope");
  }
  if (yices_error_code() != CTX_INVALID_OPERATION) {
    fail("yices_pop with no user scope did not report CTX_INVALID_OPERATION");
  }

  // While an MCSAT context has the status sat from an MCSAT check with assumptions,
  // `yices_get_model` shall return a model that gives true to each assertion and to each
  // assumption.
  expect_model_true(ctx, a, "model does not satisfy assumption a");

  yices_free_context(ctx);
}

static void test_pop_after_sat_assumptions(void) {
  context_t *ctx;
  term_t a;

  ctx = make_mcsat_context(true);
  a = yices_new_uninterpreted_term(yices_bool_type());

  // Where an MCSAT context supports push and pop, while the context has the status sat from
  // an MCSAT check with assumptions, when `yices_pop` is called, the context shall remove one
  // user scope.
  push(ctx);
  check_assuming_sat(ctx, 1, &a);
  pop_one_scope_only(ctx);

  // Where an MCSAT context supports push and pop, while the context has the status sat from
  // an MCSAT check with assumptions, when `yices_pop` is called, the context shall remove one
  // user scope.
  push(ctx);
  check_assuming_sat(ctx, 1, &a);
  check_assuming_sat(ctx, 1, &a);
  pop_one_scope_only(ctx);

  yices_free_context(ctx);
}

static void test_assert_after_sat_assumptions(void) {
  context_t *ctx;
  term_t a, b;
  model_t *mdl;

  ctx = make_mcsat_context(true);
  a = yices_new_uninterpreted_term(yices_bool_type());
  b = yices_new_uninterpreted_term(yices_bool_type());
  assert_formula(ctx, yices_or2(a, b));
  check_assuming_sat(ctx, 1, &a);

  // While an MCSAT context has the status sat from an MCSAT check with assumptions,
  // when `yices_assert_formula` is called, the context shall not keep the assumptions
  // of that check as assertions.
  assert_formula(ctx, yices_not(a));
  if (yices_check_context(ctx, NULL) != YICES_STATUS_SAT) {
    fail("assumption a is still asserted after the check with assumptions");
  }
  mdl = get_model(ctx);
  expect_true(mdl, yices_not(a), "model does not satisfy (not a)");
  expect_true(mdl, b, "model does not satisfy (or a b) with (not a)");
  yices_free_model(mdl);

  yices_free_context(ctx);
}

static void test_reset_after_sat_assumptions(void) {
  context_t *ctx;
  term_t a;

  ctx = make_mcsat_context(true);
  a = yices_new_uninterpreted_term(yices_bool_type());
  push(ctx);
  check_assuming_sat(ctx, 1, &a);

  // While an MCSAT context has the status sat from an MCSAT check with assumptions,
  // when `yices_reset_context` is called, the context shall have no user scope.
  yices_reset_context(ctx);
  if (yices_pop(ctx) >= 0) {
    fail("yices_pop succeeded after yices_reset_context");
  }
  assert_formula(ctx, yices_not(a));
  if (yices_check_context(ctx, NULL) != YICES_STATUS_SAT) {
    fail("check after yices_reset_context is not SAT");
  }
  push(ctx);
  pop_one_scope_only(ctx);

  yices_free_context(ctx);
}

static void test_labels_reused(void) {
  context_t *ctx;
  term_t a, x;
  term_t assumptions[2];
  uint32_t before;

  ctx = make_mcsat_context(false);
  a = yices_new_uninterpreted_term(yices_bool_type());
  x = yices_new_uninterpreted_term(yices_real_type());
  assumptions[0] = a;
  assumptions[1] = yices_arith_gt_atom(x, yices_int32(2));

  // Where an MCSAT context does not support push and pop, when an MCSAT check with assumptions
  // receives an assumption term that an earlier MCSAT check with assumptions received,
  // `yices_check_context_with_assumptions` shall create no label term for that assumption term.
  check_assuming(ctx, 2, assumptions, YICES_STATUS_SAT);
  before = yices_num_terms();
  check_assuming(ctx, 2, assumptions, YICES_STATUS_SAT);
  if (yices_num_terms() != before) {
    fail("a second SAT check with the same assumptions created new terms");
  }

  // Where an MCSAT context does not support push and pop, when an MCSAT check with assumptions
  // receives an assumption term that an earlier MCSAT check with assumptions received,
  // `yices_check_context_with_assumptions` shall create no label term for that assumption term.
  assert_formula(ctx, yices_not(a));
  check_assuming(ctx, 2, assumptions, YICES_STATUS_UNSAT);
  before = yices_num_terms();
  check_assuming(ctx, 2, assumptions, YICES_STATUS_UNSAT);
  if (yices_num_terms() != before) {
    fail("a second UNSAT check with the same assumptions created new terms");
  }
  expect_core_is(ctx, a, "unsat core with reused labels is not {a}");

  yices_free_context(ctx);
}

static void test_duplicate_assumption(bool pushpop) {
  context_t *ctx;
  term_t a;
  term_t assumptions[2];

  ctx = make_mcsat_context(pushpop);
  a = yices_new_uninterpreted_term(yices_bool_type());
  assumptions[0] = a;
  assumptions[1] = a;
  check_assuming_sat(ctx, 2, assumptions);

  // While an MCSAT context has the status sat from an MCSAT check with assumptions,
  // `yices_get_model` shall return a model that gives true to each assertion and to each
  // assumption.
  expect_model_true(ctx, a, "model does not satisfy assumption a");

  yices_free_context(ctx);
}

static void test_assumption_after_pop(void) {
  context_t *ctx;
  term_t a;

  ctx = make_mcsat_context(true);
  a = yices_new_uninterpreted_term(yices_bool_type());
  push(ctx);
  check_assuming_sat(ctx, 1, &a);
  pop(ctx);

  // Where an MCSAT context supports push and pop, while the context has the status sat from
  // an MCSAT check with assumptions, when `yices_push`, `yices_pop`, `yices_assert_formula`,
  // `yices_garbage_collect`, or a later check is called, the context shall remove the label
  // assertions of that check.
  assert_formula(ctx, yices_not(a));
  check_assuming(ctx, 1, &a, YICES_STATUS_UNSAT);
  expect_core_is(ctx, a, "unsat core after pop is not {a}");

  yices_free_context(ctx);
}

static void test_reset_removes_labels(bool pushpop) {
  context_t *ctx;
  term_t a;

  ctx = make_mcsat_context(pushpop);
  a = yices_new_uninterpreted_term(yices_bool_type());
  check_assuming_sat(ctx, 1, &a);

  // When `yices_reset_context` runs on an MCSAT context, the context shall remove the label
  // assertions of all earlier MCSAT checks with assumptions.
  yices_reset_context(ctx);
  assert_formula(ctx, yices_not(a));
  check_assuming(ctx, 1, &a, YICES_STATUS_UNSAT);

  yices_free_context(ctx);
}

static void test_earlier_labels_not_assumed(bool pushpop) {
  context_t *ctx;
  term_t a, b, not_a;

  ctx = make_mcsat_context(pushpop);
  a = yices_new_uninterpreted_term(yices_bool_type());
  b = yices_new_uninterpreted_term(yices_bool_type());
  not_a = yices_not(a);
  assert_formula(ctx, yices_or2(a, b));
  check_assuming_sat(ctx, 1, &a);

  // When an MCSAT check with assumptions runs, the context shall not assume the label of an
  // assumption term that the call did not receive.
  check_assuming_sat(ctx, 1, &not_a);
  expect_model_true(ctx, not_a, "model does not satisfy assumption (not a)");

  yices_free_context(ctx);
}

static uint32_t num_model_terms(context_t *ctx) {
  model_t *mdl;
  term_vector_t v;
  uint32_t n;

  mdl = get_model(ctx);
  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(mdl, &v);
  n = v.size;
  yices_delete_term_vector(&v);
  yices_free_model(mdl);
  return n;
}

static void test_labels_removed_after_sat(void) {
  context_t *ctx;
  term_t x, gt;
  uint32_t first;
  int32_t i;

  ctx = make_mcsat_context(true);
  x = yices_new_uninterpreted_term(yices_real_type());
  assert_formula(ctx, yices_arith_gt_atom(x, yices_int32(-1)));

  // Where an MCSAT context supports push and pop, while the context has the status sat from
  // an MCSAT check with assumptions, when `yices_push`, `yices_pop`, `yices_assert_formula`,
  // `yices_garbage_collect`, or a later check is called, the context shall remove the label
  // assertions of that check.
  first = 0;
  for (i = 0; i < 4; i++) {
    gt = yices_arith_gt_atom(x, yices_int32(i));
    check_assuming_sat(ctx, 1, &gt);
    if (i == 0) {
      first = num_model_terms(ctx);
    } else if (num_model_terms(ctx) != first) {
      fail("labels of earlier checks are still in the model");
    }
  }

  // Where an MCSAT context supports push and pop, while the context has the status sat from
  // an MCSAT check with assumptions, when `yices_push`, `yices_pop`, `yices_assert_formula`,
  // `yices_garbage_collect`, or a later check is called, the context shall remove the label
  // assertions of that check.
  push(ctx);
  gt = yices_arith_gt_atom(x, yices_int32(4));
  check_assuming_sat(ctx, 1, &gt);
  if (num_model_terms(ctx) != first) {
    fail("labels of the check before yices_push are still in the model");
  }
  pop_one_scope_only(ctx);

  yices_free_context(ctx);
}

/*
 * One collection for both contexts: in a debug build, a second yices_garbage_collect after one
 * that deleted a type fails the good_type assert in mark_live_types (issue #681).
 */
static void test_garbage_collect(void) {
  context_t *pp_ctx, *mc_ctx;
  term_t a, p, q, conj;
  char *before, *after;
  uint32_t i;

  pp_ctx = make_mcsat_context(true);
  a = yices_new_uninterpreted_term(yices_bool_type());
  yices_incref_term(a);
  check_assuming_sat(pp_ctx, 1, &a);

  mc_ctx = make_mcsat_context(false);
  p = yices_new_uninterpreted_term(yices_bool_type());
  q = yices_new_uninterpreted_term(yices_bool_type());
  conj = yices_and2(p, q);
  before = yices_term_to_string(conj, 80, 1, 0);
  check_assuming_sat(mc_ctx, 1, &conj);

  yices_garbage_collect(NULL, 0, NULL, 0, 0);

  // When `yices_garbage_collect` runs after an MCSAT check with assumptions, the context shall
  // keep each assertion that the user adds after the collection until the user pops the scope
  // of that assertion.
  assert_formula(pp_ctx, yices_not(a));
  if (yices_check_context(pp_ctx, NULL) != YICES_STATUS_SAT) {
    fail("check after gc is not SAT");
  }
  assert_formula(pp_ctx, yices_true());
  check_assuming(pp_ctx, 1, &a, YICES_STATUS_UNSAT);

  // Where an MCSAT context does not support push and pop, while the context holds a label for
  // an assumption term, when `yices_garbage_collect` runs, `yices_garbage_collect` shall keep
  // that assumption term and its label term.
  for (i = 0; i < 10; i++) {
    yices_new_uninterpreted_term(yices_bool_type());
  }
  after = yices_term_to_string(conj, 80, 1, 0);
  if (after == NULL || strcmp(before, after) != 0) {
    fail("yices_garbage_collect deleted an assumption term that has a label");
  }
  check_assuming_sat(mc_ctx, 1, &conj);
  expect_model_true(mc_ctx, conj, "model does not satisfy assumption (and p q) after gc");
  yices_free_string(before);
  yices_free_string(after);

  yices_decref_term(a);
  yices_free_context(mc_ctx);
  yices_free_context(pp_ctx);
}

int main(void) {
  if (! yices_has_mcsat()) {
    return 1; // skipped
  }

  yices_init();
  test_model_after_sat_assumptions();
  test_model_after_sat_arith_assumptions();
  test_pop_without_user_scope_after_sat_assumptions();
  test_pop_after_sat_assumptions();
  test_assert_after_sat_assumptions();
  test_reset_after_sat_assumptions();
  test_labels_reused();
  test_labels_removed_after_sat();
  test_garbage_collect();
  test_duplicate_assumption(true);
  test_duplicate_assumption(false);
  test_assumption_after_pop();
  test_reset_removes_labels(true);
  test_reset_removes_labels(false);
  test_earlier_labels_not_assumed(true);
  test_earlier_labels_not_assumed(false);
  yices_exit();

  return 0;
}
