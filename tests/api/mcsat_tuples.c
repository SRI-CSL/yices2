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

  yices_exit();
  return 0;
}

#else

int main(void) {
  return 1; // skipped
}

#endif
