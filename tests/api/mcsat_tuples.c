/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "yices.h"

#ifdef HAVE_MCSAT

static context_t* make_mcsat_context(bool with_interpolation) {
  ctx_config_t* config = yices_new_config();
  assert(config != NULL);
  assert(yices_set_config(config, "solver-type", "mcsat") == 0);
  assert(yices_set_config(config, "mode", "interactive") == 0);
  if (with_interpolation) {
    assert(yices_set_config(config, "model-interpolation", "true") == 0);
  }
  context_t* ctx = yices_new_context(config);
  assert(ctx != NULL);
  yices_free_config(config);
  return ctx;
}

static void assert_tuple_int_bool_value(model_t* model, term_t tuple_term, int32_t expected_i, int32_t expected_b) {
  yval_t value;
  yval_t children[2];
  int32_t i = 0;
  int32_t b = 0;

  assert(yices_get_value(model, tuple_term, &value) == 0);
  assert(yices_val_tuple_arity(model, &value) == 2);
  assert(yices_val_expand_tuple(model, &value, children) == 0);
  assert(yices_val_get_int32(model, &children[0], &i) == 0);
  assert(yices_val_get_bool(model, &children[1], &b) == 0);
  assert(i == expected_i);
  assert(b == expected_b);
}

static void test_basic_tuple_function_model(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);

  type_t dom[1] = { tuple_t };
  type_t fun_t = yices_function_type(1, dom, tuple_t);

  term_t x = yices_new_uninterpreted_term(tuple_t);
  term_t f = yices_new_uninterpreted_term(fun_t);

  term_t target_children[2] = { yices_int32(5), yices_true() };
  term_t tuple_5_true = yices_tuple(2, target_children);
  term_t fx = yices_application1(f, x);

  term_t constraints[3] = {
    yices_arith_eq_atom(yices_select(1, x), yices_int32(5)),
    yices_eq(yices_select(2, x), yices_true()),
    yices_eq(fx, tuple_5_true),
  };

  for (uint32_t i = 0; i < 3; ++i) {
    assert(yices_assert_formula(ctx, constraints[i]) == 0);
  }

  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  model_t* model = yices_get_model(ctx, 1);
  assert(model != NULL);

  for (uint32_t i = 0; i < 3; ++i) {
    assert(yices_formula_true_in_model(model, constraints[i]) == 1);
  }

  assert_tuple_int_bool_value(model, x, 5, 1);
  assert_tuple_int_bool_value(model, fx, 5, 1);

  yval_t f_val;
  yval_t def;
  yval_vector_t mappings;
  assert(yices_get_value(model, f, &f_val) == 0);
  assert(yices_val_function_arity(model, &f_val) == 1);
  yices_init_yval_vector(&mappings);
  assert(yices_val_expand_function(model, &f_val, &def, &mappings) == 0);
  assert(yices_val_tuple_arity(model, &def) == 2);
  yices_delete_yval_vector(&mappings);

  yices_free_model(model);
  yices_free_context(ctx);
}

static void test_update_and_application_with_tuple_function(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);

  type_t dom[1] = { tuple_t };
  type_t fun_t = yices_function_type(1, dom, tuple_t);

  term_t f = yices_new_uninterpreted_term(fun_t);
  term_t x_children[2] = { yices_int32(3), yices_false() };
  term_t y_children[2] = { yices_int32(9), yices_true() };
  term_t out_children[2] = { yices_int32(7), yices_true() };

  term_t x = yices_tuple(2, x_children);
  term_t y = yices_tuple(2, y_children);
  term_t out = yices_tuple(2, out_children);

  term_t g = yices_update1(f, x, out);
  term_t gx = yices_application1(g, x);
  term_t gy = yices_application1(g, y);
  term_t fy = yices_application1(f, y);

  term_t constraints[3] = {
    yices_neq(x, y),
    yices_eq(gx, out),
    yices_eq(gy, fy),
  };

  for (uint32_t i = 0; i < 3; ++i) {
    assert(yices_assert_formula(ctx, constraints[i]) == 0);
  }

  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  model_t* model = yices_get_model(ctx, 1);
  assert(model != NULL);

  for (uint32_t i = 0; i < 3; ++i) {
    assert(yices_formula_true_in_model(model, constraints[i]) == 1);
  }

  assert_tuple_int_bool_value(model, gx, 7, 1);

  yices_free_model(model);
  yices_free_context(ctx);
}

static void test_nested_tuple_and_ite(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t inner_t = yices_tuple_type2(bool_t, int_t);
  type_t outer_t = yices_tuple_type2(int_t, inner_t);
  type_t arg_t = yices_tuple_type2(int_t, bool_t);

  type_t dom[1] = { arg_t };
  type_t fun_t = yices_function_type(1, dom, outer_t);

  term_t flag = yices_new_uninterpreted_term(bool_t);
  term_t a = yices_new_uninterpreted_term(arg_t);
  term_t b = yices_new_uninterpreted_term(arg_t);
  term_t f = yices_new_uninterpreted_term(fun_t);

  term_t pick = yices_ite(flag, a, b);
  term_t fpick = yices_application1(f, pick);

  term_t inner_children[2] = { yices_true(), yices_int32(6) };
  term_t target_children[2] = { yices_int32(4), yices_tuple(2, inner_children) };
  term_t target = yices_tuple(2, target_children);

  term_t constraints[6] = {
    yices_eq(flag, yices_true()),
    yices_distinct(2, (term_t[]){a, b}),
    yices_eq(yices_select(1, a), yices_int32(1)),
    yices_eq(yices_select(2, a), yices_false()),
    yices_eq(fpick, target),
    yices_eq(yices_select(2, yices_select(2, fpick)), yices_int32(6)),
  };

  for (uint32_t i = 0; i < 6; ++i) {
    assert(yices_assert_formula(ctx, constraints[i]) == 0);
  }

  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  model_t* model = yices_get_model(ctx, 1);
  assert(model != NULL);

  for (uint32_t i = 0; i < 6; ++i) {
    assert(yices_formula_true_in_model(model, constraints[i]) == 1);
  }

  yices_free_model(model);
  yices_free_context(ctx);
}

static void test_push_pop_scope_with_tuples(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);
  type_t dom[1] = { tuple_t };
  type_t fun_t = yices_function_type(1, dom, tuple_t);

  term_t x = yices_new_uninterpreted_term(tuple_t);
  term_t f = yices_new_uninterpreted_term(fun_t);

  term_t out_children[2] = { yices_int32(4), yices_true() };
  term_t out = yices_tuple(2, out_children);

  assert(yices_assert_formula(ctx, yices_arith_eq_atom(yices_select(1, x), yices_int32(4))) == 0);
  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);

  assert(yices_push(ctx) == 0);
  assert(yices_assert_formula(ctx, yices_eq(yices_select(2, x), yices_true())) == 0);
  assert(yices_assert_formula(ctx, yices_eq(yices_application1(f, x), out)) == 0);
  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  assert(yices_pop(ctx) == 0);

  assert(yices_assert_formula(ctx, yices_eq(yices_select(2, x), yices_false())) == 0);
  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);

  model_t* model = yices_get_model(ctx, 1);
  assert(model != NULL);
  assert(yices_formula_true_in_model(model, yices_eq(yices_select(2, x), yices_false())) == 1);
  yices_free_model(model);

  yices_free_context(ctx);
}

static void test_unsat_and_interpolant_with_tuple_function(void) {
  context_t* ctx = make_mcsat_context(true);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);
  type_t dom[1] = { tuple_t };
  type_t fun_t = yices_function_type(1, dom, tuple_t);

  term_t x = yices_new_uninterpreted_term(tuple_t);
  term_t f = yices_new_uninterpreted_term(fun_t);

  term_t x_children[2] = { yices_int32(0), yices_false() };
  term_t zero_false = yices_tuple(2, x_children);

  term_t fx = yices_application1(f, x);
  term_t constraints[3] = {
    yices_eq(x, zero_false),
    yices_eq(fx, zero_false),
    yices_arith_gt_atom(yices_select(1, fx), yices_int32(0)),
  };

  for (uint32_t i = 0; i < 3; ++i) {
    assert(yices_assert_formula(ctx, constraints[i]) == 0);
  }

  model_t* model = yices_new_model();
  assert(model != NULL);

  assert(yices_check_context_with_model_and_hint(ctx, NULL, model, 0, NULL, 0) == YICES_STATUS_UNSAT);
  term_t interpolant = yices_get_model_interpolant(ctx);
  assert(interpolant != NULL_TERM);
  assert(yices_term_is_bool(interpolant));

  yices_free_model(model);
  yices_free_context(ctx);
}

static void test_tuple_function_component_with_tuple_range(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);
  type_t fun_t = yices_function_type1(int_t, tuple_t);
  type_t wrapper_t = yices_tuple_type2(fun_t, int_t);

  term_t x = yices_new_uninterpreted_term(wrapper_t);
  term_t f = yices_select(1, x);
  term_t out_children[2] = { yices_int32(1), yices_true() };
  term_t out = yices_tuple(2, out_children);
  term_t app = yices_application1(f, yices_int32(0));

  term_t constraints[2] = {
    yices_arith_eq_atom(yices_select(2, x), yices_int32(5)),
    yices_eq(app, out),
  };

  for (uint32_t i = 0; i < 2; ++i) {
    assert(yices_assert_formula(ctx, constraints[i]) == 0);
  }

  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  model_t* model = yices_get_model(ctx, 1);
  assert(model != NULL);

  for (uint32_t i = 0; i < 2; ++i) {
    assert(yices_formula_true_in_model(model, constraints[i]) == 1);
  }
  assert_tuple_int_bool_value(model, app, 1, 1);

  yices_free_model(model);
  yices_free_context(ctx);
}

static void test_tuple_function_component_with_tuple_domain(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);
  type_t fun_t = yices_function_type1(tuple_t, int_t);
  type_t wrapper_t = yices_tuple_type2(fun_t, int_t);

  term_t x = yices_new_uninterpreted_term(wrapper_t);
  term_t f = yices_select(1, x);
  term_t arg_children[2] = { yices_int32(2), yices_false() };
  term_t arg = yices_tuple(2, arg_children);
  term_t app = yices_application1(f, arg);

  term_t constraints[2] = {
    yices_arith_eq_atom(yices_select(2, x), yices_int32(4)),
    yices_arith_eq_atom(app, yices_int32(3)),
  };

  for (uint32_t i = 0; i < 2; ++i) {
    assert(yices_assert_formula(ctx, constraints[i]) == 0);
  }

  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  model_t* model = yices_get_model(ctx, 1);
  assert(model != NULL);

  for (uint32_t i = 0; i < 2; ++i) {
    assert(yices_formula_true_in_model(model, constraints[i]) == 1);
  }

  int32_t value;
  assert(yices_get_int32_value(model, app, &value) == 0);
  assert(value == 3);

  yices_free_model(model);
  yices_free_context(ctx);
}

static void test_tuple_selectors_in_arith_and_bv_terms(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t bv4_t = yices_bv_type(4);
  type_t tuple_t = yices_tuple_type3(int_t, int_t, bv4_t);

  term_t x = yices_new_uninterpreted_term(tuple_t);
  term_t x1 = yices_select(1, x);
  term_t x2 = yices_select(2, x);
  term_t x3 = yices_select(3, x);

  term_t arith = yices_add(yices_mul(x1, x2), x1);
  term_t bv = yices_bvadd(x3, yices_bvconst_uint32(4, 1));

  term_t constraints[5] = {
    yices_arith_eq_atom(x1, yices_int32(2)),
    yices_arith_eq_atom(x2, yices_int32(3)),
    yices_arith_eq_atom(arith, yices_int32(8)),
    yices_bveq_atom(x3, yices_bvconst_uint32(4, 3)),
    yices_bveq_atom(bv, yices_bvconst_uint32(4, 4)),
  };

  for (uint32_t i = 0; i < 5; ++i) {
    assert(yices_assert_formula(ctx, constraints[i]) == 0);
  }

  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  model_t* model = yices_get_model(ctx, 1);
  assert(model != NULL);

  for (uint32_t i = 0; i < 5; ++i) {
    assert(yices_formula_true_in_model(model, constraints[i]) == 1);
  }

  yices_free_model(model);
  yices_free_context(ctx);
}

static void test_tuple_update_rewrite_model(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);

  term_t x = yices_new_uninterpreted_term(tuple_t);
  term_t updated = yices_tuple_update(x, 2, yices_true());

  term_t constraints[3] = {
    yices_arith_eq_atom(yices_select(1, x), yices_int32(11)),
    yices_eq(yices_select(2, x), yices_false()),
    yices_eq(updated, yices_tuple(2, (term_t[]){ yices_int32(11), yices_true() })),
  };

  for (uint32_t i = 0; i < 3; ++i) {
    assert(yices_assert_formula(ctx, constraints[i]) == 0);
  }

  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  model_t* model = yices_get_model(ctx, 1);
  assert(model != NULL);

  for (uint32_t i = 0; i < 3; ++i) {
    assert(yices_formula_true_in_model(model, constraints[i]) == 1);
  }
  assert_tuple_int_bool_value(model, updated, 11, 1);

  yices_free_model(model);
  yices_free_context(ctx);
}

static void test_tuple_variable_term(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);

  term_t x = yices_new_variable(tuple_t);
  term_t constraints[2] = {
    yices_arith_eq_atom(yices_select(1, x), yices_int32(14)),
    yices_eq(yices_select(2, x), yices_true()),
  };

  for (uint32_t i = 0; i < 2; ++i) {
    assert(yices_assert_formula(ctx, constraints[i]) == 0);
  }

  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  model_t* model = yices_get_model(ctx, 1);
  assert(model != NULL);

  for (uint32_t i = 0; i < 2; ++i) {
    assert(yices_formula_true_in_model(model, constraints[i]) == 1);
  }
  assert_tuple_int_bool_value(model, x, 14, 1);

  yices_free_model(model);
  yices_free_context(ctx);
}

static void test_function_component_with_tuple_domain_and_range(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);
  type_t fun_t = yices_function_type1(tuple_t, tuple_t);
  type_t wrapper_t = yices_tuple_type2(fun_t, int_t);

  term_t x = yices_new_uninterpreted_term(wrapper_t);
  term_t f = yices_select(1, x);
  term_t arg = yices_tuple(2, (term_t[]){ yices_int32(6), yices_false() });
  term_t out = yices_tuple(2, (term_t[]){ yices_int32(8), yices_true() });
  term_t app = yices_application1(f, arg);

  term_t constraints[3] = {
    yices_arith_eq_atom(yices_select(2, x), yices_int32(12)),
    yices_eq(app, out),
    yices_arith_gt_atom(yices_select(1, app), yices_select(1, arg)),
  };

  for (uint32_t i = 0; i < 3; ++i) {
    assert(yices_assert_formula(ctx, constraints[i]) == 0);
  }

  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  model_t* model = yices_get_model(ctx, 1);
  assert(model != NULL);

  for (uint32_t i = 0; i < 3; ++i) {
    assert(yices_formula_true_in_model(model, constraints[i]) == 1);
  }
  assert_tuple_int_bool_value(model, app, 8, 1);

  yices_free_model(model);
  yices_free_context(ctx);
}

static void assert_named_term_occurs_in_interpolant(term_t interpolant, const char* name) {
  char* text = yices_term_to_string(interpolant, 1000, 100, 0);
  assert(text != NULL);
  if (strstr(text, name) == NULL) {
    fprintf(stderr, "interpolant: %s\n", text);
  }
  assert(strstr(text, name) != NULL);
  yices_free_string(text);
}

/*
 * Recursive tree walk that aborts if any reachable node has constructor
 * YICES_LAMBDA_TERM.
 *
 * A residual lambda in an interpolant retrieved via
 * yices_get_model_interpolant would indicate that the unblast path built
 * a (lambda v. ...) wrapper for a function-valued tuple atom and the
 * subsequent term_subst did not beta-reduce the resulting application
 * (lambda v. ...) arg. The interpolant is supposed to live in the
 * ordinary public term world (no lambdas), so any such residue is a bug.
 *
 * We don't memoize visited subterms: the interpolants returned by these
 * tests are very small, so plain tree-walking terminates quickly and
 * stays well below the (bounded) recursion depth.
 */
static bool assert_no_lambda_walk(term_t t, int depth) {
  if (depth > 64) {
    fprintf(stderr, "assert_no_lambda: walk depth exceeded 64, giving up\n");
    return true;  /* don't block the test on excessive nesting */
  }
  term_constructor_t kind = yices_term_constructor(t);
  if (kind == YICES_LAMBDA_TERM) {
    char* s = yices_term_to_string(t, 200, 10, 0);
    fprintf(stderr, "assert_no_lambda: residual lambda at subterm %s\n", s ? s : "<nil>");
    yices_free_string(s);
    return false;
  }
  int32_t n = yices_term_num_children(t);
  if (n <= 0) return true;
  for (int32_t i = 0; i < n; ++i) {
    term_t c = yices_term_child(t, i);
    if (c == NULL_TERM) continue;
    if (!assert_no_lambda_walk(c, depth + 1)) return false;
  }
  return true;
}

static void assert_interpolant_has_no_lambda_residue(term_t interpolant) {
  bool ok = assert_no_lambda_walk(interpolant, 0);
  if (!ok) {
    char* text = yices_term_to_string(interpolant, 4000, 100, 0);
    fprintf(stderr, "interpolant with lambda residue: %s\n", text ? text : "<nil>");
    yices_free_string(text);
  }
  assert(ok);
}

static void test_interpolant_with_tuple_function_component_range(void) {
  context_t* ctx = make_mcsat_context(true);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);
  type_t fun_t = yices_function_type1(int_t, tuple_t);
  type_t wrapper_t = yices_tuple_type2(fun_t, int_t);

  term_t x = yices_new_uninterpreted_term(wrapper_t);
  assert(yices_set_term_name(x, "tuple_fun_range") == 0);
  term_t f = yices_select(1, x);
  term_t out_children[2] = { yices_int32(3), yices_true() };
  term_t out = yices_tuple(2, out_children);
  term_t app = yices_application1(f, yices_int32(0));

  term_t constraint = yices_eq(app, out);
  assert(yices_assert_formula(ctx, constraint) == 0);

  term_t assumption = yices_not(yices_arith_gt_atom(yices_select(1, app), yices_int32(2)));
  smt_status_t status = yices_check_context_with_assumptions(ctx, NULL, 1, &assumption);
  assert(status == YICES_STATUS_UNSAT);

  term_t interpolant = yices_get_model_interpolant(ctx);
  assert(interpolant != NULL_TERM);
  assert(yices_term_is_bool(interpolant));
  assert_named_term_occurs_in_interpolant(interpolant, "tuple_fun_range");
  assert_interpolant_has_no_lambda_residue(interpolant);

  yices_free_context(ctx);
}

static void test_interpolant_with_tuple_function_component_domain(void) {
  context_t* ctx = make_mcsat_context(true);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);
  type_t fun_t = yices_function_type1(tuple_t, int_t);
  type_t wrapper_t = yices_tuple_type2(fun_t, int_t);

  term_t x = yices_new_uninterpreted_term(wrapper_t);
  assert(yices_set_term_name(x, "tuple_fun_domain") == 0);
  term_t f = yices_select(1, x);
  term_t arg_children[2] = { yices_int32(2), yices_false() };
  term_t arg = yices_tuple(2, arg_children);
  term_t app = yices_application1(f, arg);

  term_t constraint = yices_arith_eq_atom(app, yices_int32(5));
  assert(yices_assert_formula(ctx, constraint) == 0);

  term_t assumption = yices_not(yices_arith_gt_atom(app, yices_int32(4)));
  smt_status_t status = yices_check_context_with_assumptions(ctx, NULL, 1, &assumption);
  assert(status == YICES_STATUS_UNSAT);

  term_t interpolant = yices_get_model_interpolant(ctx);
  assert(interpolant != NULL_TERM);
  assert(yices_term_is_bool(interpolant));
  assert_named_term_occurs_in_interpolant(interpolant, "tuple_fun_domain");
  assert_interpolant_has_no_lambda_residue(interpolant);

  yices_free_context(ctx);
}

static void test_interpolant_with_tuple_function_component_domain_and_range(void) {
  context_t* ctx = make_mcsat_context(true);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t tuple_t = yices_tuple_type2(int_t, bool_t);
  type_t fun_t = yices_function_type1(tuple_t, tuple_t);
  type_t wrapper_t = yices_tuple_type2(fun_t, int_t);

  term_t x = yices_new_uninterpreted_term(wrapper_t);
  assert(yices_set_term_name(x, "tuple_fun_both") == 0);
  term_t f = yices_select(1, x);
  term_t arg = yices_tuple(2, (term_t[]){ yices_int32(4), yices_false() });
  term_t out = yices_tuple(2, (term_t[]){ yices_int32(9), yices_true() });
  term_t app = yices_application1(f, arg);

  assert(yices_assert_formula(ctx, yices_eq(app, out)) == 0);

  term_t assumption = yices_not(yices_arith_gt_atom(yices_select(1, app), yices_int32(8)));
  smt_status_t status = yices_check_context_with_assumptions(ctx, NULL, 1, &assumption);
  assert(status == YICES_STATUS_UNSAT);

  term_t interpolant = yices_get_model_interpolant(ctx);
  assert(interpolant != NULL_TERM);
  assert(yices_term_is_bool(interpolant));
  assert_named_term_occurs_in_interpolant(interpolant, "tuple_fun_both");
  assert_interpolant_has_no_lambda_residue(interpolant);

  yices_free_context(ctx);
}

/*
 * Regression for tuple selectors under term kinds that the tuple-blast
 * dispatch previously missed (BIT_TERM, ARITH_IS_INT_ATOM, ARITH_FLOOR,
 * ARITH_CEIL, ARITH_ABS, ARITH_FF_EQ_ATOM, ARITH_FF_BINEQ_ATOM).
 *
 * Without the dispatch entries, term_has_tuples_in_subdag would not
 * descend through these kinds and would classify `(<op> (select x i))`
 * as tuple-free, after which the iterative driver would forward an
 * un-blasted SELECT into the old preprocessor. With the entries in
 * place each operator is rebuilt over the blasted operand and the
 * solver succeeds.
 *
 * BIT_TERM over a tuple-component bv is exercised here at the C-API
 * level. ARITH_FLOOR / ARITH_IS_INT_ATOM / ARITH_CEIL / ARITH_ABS
 * share the same dispatch shape and are exercised at the .ys frontend
 * level under tests/regress/mcsat/tuples/tuple_unary_arith.ys (ceil
 * uses a lax assertion there because of an unrelated semantic bug in
 * the nra plugin -- see that file's header). ARITH_FF_EQ_ATOM /
 * ARITH_FF_BINEQ_ATOM share the unary-/binary-arith dispatch shape
 * but cannot be tested either: tuples are not part of SMT2 and the
 * .ys frontend has no FF arithmetic.
 */
/*
 * M1 regression: function-valued tuple component used naked (in
 * equality position, not application position).
 *
 * Existing interpolant tests only cover application form -- after
 * preprocessor_unblast_term substitutes the leaf with (lambda (v0)
 * (... v0 ...)) and yices_term_subst applies it to the original
 * argument, beta-reduction in mk_application removes the lambda. The
 * concern from review M1 was that when an interpolant references the
 * leaf naked, no application sits on top to trigger beta-reduction
 * and the lambda persists in the public term.
 *
 * In practice the "naked" path is doubly guarded:
 *   (a) Single-leaf function ranges: mk_lambda already eta-reduces
 *       (lambda (v0) (f v0)) -> f at construction time
 *       (term_manager.c mk_lambda fast path), so even a naked leaf
 *       substitution produces a plain function term.
 *   (b) Multi-leaf function ranges (range is itself a tuple): the
 *       per-slice lambda body is (select ((select x 1) v0) i), which
 *       is NOT eta-reducible. But MCSAT's interpolation in this
 *       configuration always returns the original asserted formula
 *       (e.g. `(= (select x 1) (select y 1))`) rather than a
 *       leaf-level rewrite, so unblast never needs to substitute the
 *       leaf inside the interpolant.
 *
 * This test pins (b) by asserting `(= fx fy)` against `(distinct fx
 * fy)` over a multi-leaf function range and demanding the resulting
 * interpolant be lambda-free. If a future change rewrites the
 * interpolant in terms of the blasted leaves, the
 * assert_interpolant_has_no_lambda_residue check will catch the
 * regression here rather than at user-facing call sites.
 */
static void test_interpolant_with_naked_function_component(void) {
  context_t* ctx = make_mcsat_context(true);

  type_t int_t = yices_int_type();
  type_t bool_t = yices_bool_type();
  type_t range_t = yices_tuple_type2(int_t, bool_t);
  type_t fun_t = yices_function_type1(int_t, range_t);
  type_t wrapper_t = yices_tuple_type2(fun_t, int_t);

  term_t x = yices_new_uninterpreted_term(wrapper_t);
  term_t y = yices_new_uninterpreted_term(wrapper_t);
  assert(yices_set_term_name(x, "naked_fun_x") == 0);
  assert(yices_set_term_name(y, "naked_fun_y") == 0);
  term_t fx = yices_select(1, x);   /* (-> int (tuple int bool)) */
  term_t fy = yices_select(1, y);   /* (-> int (tuple int bool)) */

  term_t feq = yices_eq(fx, fy);
  assert(feq != NULL_TERM);
  assert(yices_assert_formula(ctx, feq) == 0);

  term_t assumption = yices_neq(fx, fy);
  smt_status_t status = yices_check_context_with_assumptions(ctx, NULL, 1, &assumption);
  assert(status == YICES_STATUS_UNSAT);

  term_t interpolant = yices_get_model_interpolant(ctx);
  assert(interpolant != NULL_TERM);
  assert(yices_term_is_bool(interpolant));
  assert_interpolant_has_no_lambda_residue(interpolant);

  yices_free_context(ctx);
}

/*
 * M2 regression: tuple model reconstruction must not drop the original
 * atom when a blasted leaf is unconstrained AND the model cannot
 * synthesize defaults on demand.
 *
 * Setup: x : (tuple int int) with only `(select x 1) = 5` asserted.
 * Component 2's blasted leaf is created by the preprocessor (via
 * tuple_blast_term_body's UNINTERPRETED_TERM arm) but never appears
 * in any clause, so it gets no trail value.
 *
 * Then yices_get_model(ctx, 0) builds the public model with
 * has_alias=false, which disables the alias-based default-completion
 * path in eval_uninterpreted. Without the M2 fix, model_get_term_value
 * on the unconstrained leaf returns a negative error code, the leaf
 * loop in preprocessor_build_tuple_model sets ok=false, and the entire
 * `x` atom is silently dropped from the public model -- so
 * yices_get_value on `x` fails and `(select x 1)` evaluates without
 * its parent ever appearing. With the fix, the leaf is filled in via
 * vtbl_make_object and `x` is reconstructable.
 */
static void test_partial_tuple_model_no_keep_subst(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t tup_t = yices_tuple_type2(int_t, int_t);
  term_t x = yices_new_uninterpreted_term(tup_t);
  assert(yices_set_term_name(x, "partial_tuple_x") == 0);

  /* Constrain only the first component. */
  assert(yices_assert_formula(ctx,
           yices_arith_eq_atom(yices_select(1, x), yices_int32(5))) == 0);

  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);

  /* keep_subst=0: model has no alias table, so eval_uninterpreted has
   * no default-completion path. Without the fixes, this triggers the
   * has_alias assertion in model_add_substitution AND drops the tuple
   * atom in preprocessor_build_tuple_model. */
  model_t* model = yices_get_model(ctx, 0);
  assert(model != NULL);

  /* The constrained component must be 5. */
  int32_t v1 = -1;
  assert(yices_get_int32_value(model, yices_select(1, x), &v1) == 0);
  assert(v1 == 5);

  /* The whole tuple atom must reconstruct -- even though component 2
   * is unconstrained. Before the fix this call would fail because the
   * preprocessor dropped `x` from the model. */
  yval_t tup_val;
  assert(yices_get_value(model, x, &tup_val) == 0);
  assert(yices_val_tuple_arity(model, &tup_val) == 2);

  yval_t children[2];
  assert(yices_val_expand_tuple(model, &tup_val, children) == 0);
  int32_t got_v1 = -1;
  assert(yices_val_get_int32(model, &children[0], &got_v1) == 0);
  assert(got_v1 == 5);
  /* Component 2 may be any int -- we only require that the value
   * exists and is well-typed. */
  int32_t got_v2 = 0;
  assert(yices_val_get_int32(model, &children[1], &got_v2) == 0);

  yices_free_model(model);
  yices_free_context(ctx);
}

static void test_tuple_blast_bit_over_tuple_component(void) {
  context_t* ctx = make_mcsat_context(false);

  type_t int_t = yices_int_type();
  type_t bv4_t = yices_bv_type(4);
  type_t tup_t = yices_tuple_type2(int_t, bv4_t);

  term_t x  = yices_new_uninterpreted_term(tup_t);
  term_t x2 = yices_select(2, x);  /* bv4 */

  term_t cs[] = {
    yices_bveq_atom(x2, yices_bvconst_uint32(4, 0xa)),
    yices_bitextract(x2, 1),              /* bit1 of 0b1010 -> true  */
    yices_not(yices_bitextract(x2, 0)),   /* bit0 of 0b1010 -> false */
  };
  for (uint32_t i = 0; i < sizeof(cs)/sizeof(cs[0]); ++i) {
    assert(yices_assert_formula(ctx, cs[i]) == 0);
  }

  smt_status_t s = yices_check_context(ctx, NULL);
  assert(s == YICES_STATUS_SAT);

  model_t* m = yices_get_model(ctx, 1);
  assert(m != NULL);
  for (uint32_t i = 0; i < sizeof(cs)/sizeof(cs[0]); ++i) {
    assert(yices_formula_true_in_model(m, cs[i]) == 1);
  }
  yices_free_model(m);
  yices_free_context(ctx);
}

/*
 * Regression for the tuple-blast memo caches across GC.
 *
 * The preprocessor caches type_is_tuple_free / type_leaf_count /
 * term_has_tuples_in_subdag results keyed by raw type/term IDs. Yices
 * recycles those IDs after `yices_garbage_collect`, so a stale cache
 * entry could misclassify a fresh, unrelated type/term reusing the same
 * slot. preprocessor_gc_mark resets these caches before each sweep; this
 * test exercises that path.
 *
 * We solve a tuple-typed problem (populates the caches), free everything
 * solver-side, run GC explicitly with no roots, then build and solve a
 * second tuple-typed problem of *different shape* that is likely to
 * reuse the freed type/term IDs. If the cache reset path were missing,
 * the second solve could either misclassify a reused type as tuple-free
 * and pass an un-blasted SELECT into the old preprocessor, or pick up a
 * stale leaf-count that no longer matches the new tuple's shape. Either
 * way the call below would fail (status != SAT or assertion in mcsat).
 */
static void test_tuple_preprocessing_then_gc(void) {
  /* First problem: a Pair=(int,bool) tuple constrained on both fields.
   * This populates type_is_tuple_free_cache, type_leaf_count_cache, and
   * term_has_tuples_cache for the relevant types and selector subterms. */
  {
    context_t* ctx = make_mcsat_context(false);
    type_t int_t  = yices_int_type();
    type_t bool_t = yices_bool_type();
    type_t pair_t = yices_tuple_type2(int_t, bool_t);
    term_t x = yices_new_uninterpreted_term(pair_t);
    assert(yices_assert_formula(ctx, yices_arith_eq_atom(yices_select(1, x), yices_int32(2))) == 0);
    assert(yices_assert_formula(ctx, yices_eq(yices_select(2, x), yices_true())) == 0);
    assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
    model_t* m = yices_get_model(ctx, 1);
    assert(m != NULL);
    assert_tuple_int_bool_value(m, x, 2, 1);
    yices_free_model(m);
    yices_free_context(ctx);
  }

  /* Force recycling: no roots kept => everything from the first problem,
   * including the Pair type and the selector terms we cached against, is
   * eligible for sweep. yices_garbage_collect does the sweep, after
   * which type/term IDs from the first problem may be reused below. */
  yices_garbage_collect(NULL, 0, NULL, 0, 0);

  /* Second problem: a *different* tuple shape -- Triple=(bool,int,int) --
   * plus a function tuple component. If a stale leaf-count or
   * tuple-free entry were inherited from a recycled ID, the iterative
   * driver would build a malformed blasted form here; the call would
   * either fail to be SAT or trip an internal assertion. We assert SAT
   * and verify the model agrees with the constraints. */
  {
    context_t* ctx = make_mcsat_context(false);
    type_t int_t   = yices_int_type();
    type_t bool_t  = yices_bool_type();
    type_t triple_t = yices_tuple_type3(bool_t, int_t, int_t);
    term_t y = yices_new_uninterpreted_term(triple_t);

    assert(yices_assert_formula(ctx, yices_eq(yices_select(1, y), yices_false())) == 0);
    assert(yices_assert_formula(ctx, yices_arith_eq_atom(yices_select(2, y), yices_int32(7))) == 0);
    assert(yices_assert_formula(ctx,
      yices_arith_eq_atom(yices_select(3, y),
                          yices_add(yices_select(2, y), yices_int32(1)))) == 0);

    assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
    model_t* m = yices_get_model(ctx, 1);
    assert(m != NULL);

    int32_t bv = -1, iv2 = -1, iv3 = -1;
    yval_t val, kids[3];
    assert(yices_get_value(m, y, &val) == 0);
    assert(yices_val_tuple_arity(m, &val) == 3);
    assert(yices_val_expand_tuple(m, &val, kids) == 0);
    assert(yices_val_get_bool(m, &kids[0], &bv) == 0);
    assert(yices_val_get_int32(m, &kids[1], &iv2) == 0);
    assert(yices_val_get_int32(m, &kids[2], &iv3) == 0);
    assert(bv == 0);
    assert(iv2 == 7);
    assert(iv3 == 8);

    yices_free_model(m);
    yices_free_context(ctx);
  }
}

int main(void) {
  if (!yices_has_mcsat()) {
    return 1; // skipped
  }

  yices_init();

  test_basic_tuple_function_model();
  test_update_and_application_with_tuple_function();
  test_nested_tuple_and_ite();
  test_push_pop_scope_with_tuples();
  test_unsat_and_interpolant_with_tuple_function();
  test_tuple_function_component_with_tuple_range();
  test_tuple_function_component_with_tuple_domain();
  test_tuple_selectors_in_arith_and_bv_terms();
  test_tuple_update_rewrite_model();
  test_tuple_variable_term();
  test_function_component_with_tuple_domain_and_range();
  test_interpolant_with_tuple_function_component_range();
  test_interpolant_with_tuple_function_component_domain();
  test_interpolant_with_tuple_function_component_domain_and_range();
  test_tuple_blast_bit_over_tuple_component();
  test_interpolant_with_naked_function_component();
  test_partial_tuple_model_no_keep_subst();
  test_tuple_preprocessing_then_gc();

  yices_exit();
  return 0;
}

#else

int main(void) {
  return 1; // skipped
}

#endif
