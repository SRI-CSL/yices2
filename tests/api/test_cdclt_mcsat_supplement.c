/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * API coverage for CDCL(T) with supplementary MCSAT.
 *
 * This test intentionally forces top-level solver-type=dpllt and exercises:
 * - nonlinear arithmetic handled via supplementary MCSAT
 * - finite-field constraints handled via supplementary MCSAT
 * - assumptions + unsat-core extraction on unsupported atoms
 * - push/pop lifecycle on supplemental formulas
 * - supplementary check-mode parameter (both/final-only)
 * - division-by-zero behavior remains a front-end error path
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <gmp.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <yices.h>

static void fail(const char *msg) {
  fprintf(stderr, "FAIL: %s\n", msg);
  yices_print_error(stderr);
  exit(2);
}

static void check(bool cond, const char *msg) {
  if (!cond) {
    fail(msg);
  }
}

static void check_code(int32_t code, const char *msg) {
  if (code < 0) {
    fail(msg);
  }
}

static void check_status(smt_status_t actual, smt_status_t expected, const char *msg) {
  if (actual != expected) {
    fail(msg);
  }
}

static bool has_term(const term_vector_t *v, term_t t) {
  uint32_t i;

  for (i = 0; i < v->size; i++) {
    if (v->data[i] == t) {
      return true;
    }
  }
  return false;
}

static context_t *make_cdclt_context(const char *logic_name) {
  ctx_config_t *cfg;
  context_t *ctx;
  int32_t code;

  cfg = yices_new_config();
  if (cfg == NULL) {
    fail("yices_new_config failed");
  }

  if (logic_name != NULL) {
    code = yices_default_config_for_logic(cfg, logic_name);
    if (code < 0) {
      yices_free_config(cfg);
      fail("yices_default_config_for_logic failed");
    }
  }

  code = yices_set_config(cfg, "solver-type", "dpllt");
  if (code < 0) {
    yices_free_config(cfg);
    fail("setting solver-type=dpllt failed");
  }

  code = yices_set_config(cfg, "mcsat-supplement", "true");
  if (code < 0) {
    yices_free_config(cfg);
    fail("setting mcsat-supplement=true failed");
  }

  code = yices_set_config(cfg, "mode", "push-pop");
  if (code < 0) {
    yices_free_config(cfg);
    fail("setting mode=push-pop failed");
  }

  ctx = yices_new_context(cfg);
  yices_free_config(cfg);
  if (ctx == NULL) {
    fail("yices_new_context failed");
  }

  return ctx;
}

static term_t ff_const_si(long val, long mod) {
  mpz_t zval, zmod;
  term_t t;

  mpz_init_set_si(zval, val);
  mpz_init_set_si(zmod, mod);
  t = yices_ff_const(zval, zmod);
  mpz_clear(zmod);
  mpz_clear(zval);
  return t;
}

static void test_nla_sat_unsat_and_model(void) {
  context_t *ctx;
  term_t x, xx, eq4, eq2, eq3;
  smt_status_t stat;
  model_t *mdl;
  int64_t v;

  ctx = make_cdclt_context("QF_UFLIA");

  x = yices_new_uninterpreted_term(yices_int_type());
  xx = yices_mul(x, x);
  eq4 = yices_arith_eq_atom(xx, yices_int32(4));
  check(eq4 != NULL_TERM, "building nonlinear equation failed");

  check_code(yices_assert_formula(ctx, eq4), "assert x*x=4 failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_SAT, "expected SAT for x*x=4");

  mdl = yices_get_model(ctx, 1);
  check(mdl != NULL, "yices_get_model failed on SAT nonlinear context");
  check(yices_formula_true_in_model(mdl, eq4) == 1, "model must satisfy x*x=4");
  check_code(yices_get_int64_value(mdl, xx, &v), "reading value of x*x failed");
  check(v == 4, "expected model value x*x = 4");
  yices_free_model(mdl);

  yices_reset_context(ctx);
  eq2 = yices_arith_eq_atom(xx, yices_int32(2));
  eq3 = yices_arith_eq_atom(xx, yices_int32(3));
  check_code(yices_assert_formula(ctx, eq2), "assert x*x=2 failed");
  check_code(yices_assert_formula(ctx, eq3), "assert x*x=3 failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_UNSAT, "expected UNSAT for x*x=2 and x*x=3");

  yices_free_context(ctx);
}

static void test_nla_hidden_product_and_push_pop(void) {
  context_t *ctx;
  term_t x, y, xy, ge5, xle1, yle1, xge0, yge0, eq2, eq1, xeq1;
  smt_status_t stat;

  ctx = make_cdclt_context("QF_UFLIA");
  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  xy = yices_mul(x, y);

  ge5 = yices_arith_geq_atom(xy, yices_int32(5));
  xle1 = yices_arith_leq_atom(x, yices_int32(1));
  yle1 = yices_arith_leq_atom(y, yices_int32(1));
  xge0 = yices_arith_geq_atom(x, yices_int32(0));
  yge0 = yices_arith_geq_atom(y, yices_int32(0));

  check_code(yices_assert_formula(ctx, ge5), "assert x*y>=5 failed");
  check_code(yices_assert_formula(ctx, xle1), "assert x<=1 failed");
  check_code(yices_assert_formula(ctx, yle1), "assert y<=1 failed");
  check_code(yices_assert_formula(ctx, xge0), "assert x>=0 failed");
  check_code(yices_assert_formula(ctx, yge0), "assert y>=0 failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_UNSAT, "expected UNSAT for hidden-product constraints");

  yices_reset_context(ctx);

  check_code(yices_push(ctx), "push failed");
  eq2 = yices_arith_eq_atom(yices_mul(x, x), yices_int32(2));
  check_code(yices_assert_formula(ctx, eq2), "assert x*x=2 failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_UNSAT, "expected UNSAT for integer x*x=2");
  check_code(yices_pop(ctx), "pop failed");

  check_code(yices_push(ctx), "second push failed");
  eq1 = yices_arith_eq_atom(yices_mul(x, x), yices_int32(1));
  xeq1 = yices_arith_eq_atom(x, yices_int32(1));
  check_code(yices_assert_formula(ctx, eq1), "assert x*x=1 failed");
  check_code(yices_assert_formula(ctx, xeq1), "assert x=1 failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_SAT, "expected SAT for x*x=1 and x=1");
  check_code(yices_pop(ctx), "second pop failed");

  yices_free_context(ctx);
}

static void test_nonconstant_divisor_and_param_modes(void) {
  context_t *ctx;
  param_t *params;
  term_t x, y;
  term_t yeq2, xeq6, div_eq3, div_eq4;
  smt_status_t stat;
  model_t *mdl;

  ctx = make_cdclt_context("QF_UFLRA");
  x = yices_new_uninterpreted_term(yices_real_type());
  y = yices_new_uninterpreted_term(yices_real_type());

  yeq2 = yices_arith_eq_atom(y, yices_rational32(2, 1));
  xeq6 = yices_arith_eq_atom(x, yices_rational32(6, 1));
  div_eq3 = yices_arith_eq_atom(yices_division(x, y), yices_rational32(3, 1));
  div_eq4 = yices_arith_eq_atom(yices_division(x, y), yices_rational32(4, 1));

  params = yices_new_param_record();
  check(params != NULL, "yices_new_param_record failed");
  yices_default_params_for_context(ctx, params);

  check_code(yices_set_param(params, "mcsat-supplement-check", "final-only"),
             "set_param(final-only) failed");
  check_code(yices_assert_formula(ctx, yeq2), "assert y=2 failed");
  check_code(yices_assert_formula(ctx, xeq6), "assert x=6 failed");
  check_code(yices_assert_formula(ctx, div_eq3), "assert x/y=3 failed");
  stat = yices_check_context(ctx, params);
  check_status(stat, YICES_STATUS_SAT, "expected SAT for x=6,y=2,x/y=3");

  mdl = yices_get_model(ctx, 1);
  check(mdl != NULL, "get_model failed for nonconstant-divisor SAT");
  check(yices_formula_true_in_model(mdl, div_eq3) == 1, "model must satisfy x/y=3");
  yices_free_model(mdl);

  yices_reset_context(ctx);

  check_code(yices_set_param(params, "mcsat-supplement-check", "both"),
             "set_param(both) failed");
  check_code(yices_assert_formula(ctx, yeq2), "reassert y=2 failed");
  check_code(yices_assert_formula(ctx, xeq6), "reassert x=6 failed");
  check_code(yices_assert_formula(ctx, div_eq4), "assert x/y=4 failed");
  stat = yices_check_context(ctx, params);
  check_status(stat, YICES_STATUS_UNSAT, "expected UNSAT for x=6,y=2,x/y=4");

  yices_free_param_record(params);
  yices_free_context(ctx);
}

static void test_ff_sat_unsat_model_and_assumption_core(void) {
  context_t *ctx;
  mpz_t p, val, mod, tmp;
  type_t tau;
  term_t a, c1, c3, sat_eq, ff_eq, ff_neq;
  term_t pa, qa, imp1, imp2;
  term_t assumptions[2];
  term_vector_t core;
  smt_status_t stat;
  model_t *mdl;

  mpz_init_set_si(p, 7);
  mpz_init(val);
  mpz_init(mod);
  mpz_init(tmp);

  ctx = make_cdclt_context(NULL);
  tau = yices_ff_type(p);
  check(tau != NULL_TYPE, "creating FF type failed");
  a = yices_new_uninterpreted_term(tau);
  check(a != NULL_TERM, "creating FF variable failed");

  c1 = ff_const_si(1, 7);
  c3 = ff_const_si(3, 7);
  sat_eq = yices_ff_eq_atom(yices_ff_add(a, c1), c3);
  check(sat_eq != NULL_TERM, "building FF SAT constraint failed");

  check_code(yices_assert_formula(ctx, sat_eq), "assert FF SAT constraint failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_SAT, "expected SAT for a+1=3 in F7");

  mdl = yices_get_model(ctx, 1);
  check(mdl != NULL, "get_model failed for FF SAT");
  check_code(yices_get_ff_value(mdl, a, val, mod), "get_ff_value failed");
  check(mpz_cmp_si(mod, 7) == 0, "expected FF modulus 7");
  mpz_mod(tmp, val, mod);
  check(mpz_cmp_si(tmp, 2) == 0, "expected a = 2 mod 7");
  check(yices_formula_true_in_model(mdl, sat_eq) == 1, "model must satisfy a+1=3");
  yices_free_model(mdl);

  yices_reset_context(ctx);

  ff_eq = yices_ff_eq_atom(a, c1);
  ff_neq = yices_ff_neq_atom(a, c1);
  check_code(yices_assert_formula(ctx, ff_eq), "assert a=1 failed");
  check_code(yices_assert_formula(ctx, ff_neq), "assert a!=1 failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_UNSAT, "expected UNSAT for a=1 and a!=1");

  yices_reset_context(ctx);

  pa = yices_new_uninterpreted_term(yices_bool_type());
  qa = yices_new_uninterpreted_term(yices_bool_type());
  imp1 = yices_implies(pa, yices_ff_eq_atom(a, c1));
  imp2 = yices_implies(qa, yices_ff_neq_atom(a, c1));
  check_code(yices_assert_formula(ctx, imp1), "assert implication pa=>a=1 failed");
  check_code(yices_assert_formula(ctx, imp2), "assert implication qa=>a!=1 failed");

  assumptions[0] = pa;
  assumptions[1] = qa;
  stat = yices_check_context_with_assumptions(ctx, NULL, 2, assumptions);
  check_status(stat, YICES_STATUS_UNSAT, "expected UNSAT with FF assumptions pa,qa");

  yices_init_term_vector(&core);
  check_code(yices_get_unsat_core(ctx, &core), "yices_get_unsat_core failed for FF assumptions");
  check(core.size == 2, "expected two assumptions in FF unsat core");
  check(has_term(&core, pa) && has_term(&core, qa), "FF unsat core missing assumptions");
  yices_delete_term_vector(&core);

  yices_free_context(ctx);
  mpz_clear(tmp);
  mpz_clear(mod);
  mpz_clear(val);
  mpz_clear(p);
}

static void test_nla_assumption_core(void) {
  context_t *ctx;
  term_t x, p, q;
  term_t imp1, imp2;
  term_t assumptions[2];
  term_vector_t core;
  smt_status_t stat;

  ctx = make_cdclt_context("QF_UFLRA");
  x = yices_new_uninterpreted_term(yices_real_type());
  p = yices_new_uninterpreted_term(yices_bool_type());
  q = yices_new_uninterpreted_term(yices_bool_type());

  imp1 = yices_implies(p, yices_arith_eq_atom(yices_mul(x, x), yices_rational32(2, 1)));
  imp2 = yices_implies(q, yices_arith_eq_atom(yices_mul(x, x), yices_rational32(3, 1)));
  check_code(yices_assert_formula(ctx, imp1), "assert p=>x*x=2 failed");
  check_code(yices_assert_formula(ctx, imp2), "assert q=>x*x=3 failed");

  assumptions[0] = p;
  assumptions[1] = q;
  stat = yices_check_context_with_assumptions(ctx, NULL, 2, assumptions);
  check_status(stat, YICES_STATUS_UNSAT, "expected UNSAT with NLA assumptions p,q");

  yices_init_term_vector(&core);
  check_code(yices_get_unsat_core(ctx, &core), "yices_get_unsat_core failed for NLA assumptions");
  check(core.size == 2, "expected two assumptions in NLA unsat core");
  check(has_term(&core, p) && has_term(&core, q), "NLA unsat core missing assumptions");
  yices_delete_term_vector(&core);

  yices_free_context(ctx);
}

static void test_simplex_relaxation_phase2(void) {
  context_t *ctx;
  term_t x, y, xy, yx;
  term_t ge1, le0, xeq0, gt0, xeq2, yeq2, eq4;
  smt_status_t stat;
  model_t *mdl;
  int32_t v32;

  ctx = make_cdclt_context("QF_UFLIA");
  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  xy = yices_mul(x, y);
  yx = yices_mul(y, x);

  /*
   * The relaxation should canonicalize (* x y) and (* y x) to the same
   * internal simplex variable; exact MCSAT remains the final authority.
   */
  ge1 = yices_arith_geq_atom(xy, yices_int32(1));
  le0 = yices_arith_leq_atom(yx, yices_int32(0));
  check_code(yices_assert_formula(ctx, ge1), "assert x*y>=1 failed");
  check_code(yices_assert_formula(ctx, le0), "assert y*x<=0 failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_UNSAT, "expected UNSAT for canonicalized product relaxation");

  yices_reset_context(ctx);

  /*
   * The linear relaxation is satisfiable here (p_xy > 0 with x = 0), so
   * the exact MCSAT satellite must still run after simplex.
   */
  xeq0 = yices_arith_eq_atom(x, yices_int32(0));
  gt0 = yices_arith_gt_atom(xy, yices_int32(0));
  check_code(yices_assert_formula(ctx, xeq0), "assert x=0 failed");
  check_code(yices_assert_formula(ctx, gt0), "assert x*y>0 failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_UNSAT, "expected exact MCSAT UNSAT after satisfiable relaxation");

  yices_reset_context(ctx);

  xeq2 = yices_arith_eq_atom(x, yices_int32(2));
  yeq2 = yices_arith_eq_atom(y, yices_int32(2));
  eq4 = yices_arith_eq_atom(xy, yices_int32(4));
  check_code(yices_assert_formula(ctx, xeq2), "assert x=2 failed");
  check_code(yices_assert_formula(ctx, yeq2), "assert y=2 failed");
  check_code(yices_assert_formula(ctx, eq4), "assert x*y=4 failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_SAT, "expected SAT for relaxed product with exact MCSAT model");
  mdl = yices_get_model(ctx, 1);
  check(mdl != NULL, "get_model failed for Phase-2 relaxation SAT case");
  check(yices_formula_true_in_model(mdl, eq4) == 1, "model must satisfy exact x*y=4");
  check_code(yices_get_int32_value(mdl, xy, &v32), "model must define exact x*y");
  check(v32 == 4, "model value for exact x*y must be 4");
  yices_free_model(mdl);

  yices_free_context(ctx);
}

static void test_mcsat_model_values_drive_egraph_model(void) {
  context_t *ctx;
  type_t real_type, f_type;
  term_t x, f, xx, fx, eq4, feq7;
  smt_status_t stat;
  model_t *mdl;
  int64_t num;
  uint64_t den;

  ctx = make_cdclt_context("QF_UFLRA");
  real_type = yices_real_type();
  f_type = yices_function_type1(real_type, real_type);
  check(f_type != NULL_TYPE, "building real->real type failed");

  x = yices_new_uninterpreted_term(real_type);
  f = yices_new_uninterpreted_term(f_type);
  xx = yices_mul(x, x);
  fx = yices_application1(f, x);
  eq4 = yices_arith_eq_atom(xx, yices_rational32(4, 1));
  feq7 = yices_arith_eq_atom(fx, yices_rational32(7, 1));

  check_code(yices_assert_formula(ctx, eq4), "assert x*x=4 failed in model-provider test");
  check_code(yices_assert_formula(ctx, feq7), "assert f(x)=7 failed in model-provider test");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_SAT, "expected SAT for x*x=4 and f(x)=7");

  mdl = yices_get_model(ctx, 1);
  check(mdl != NULL, "get_model failed in model-provider test");
  check(yices_formula_true_in_model(mdl, eq4) == 1, "model must satisfy x*x=4");
  check(yices_formula_true_in_model(mdl, feq7) == 1, "function model must be keyed by MCSAT's x value");
  check_code(yices_get_rational64_value(mdl, x, &num, &den), "model must define x from MCSAT");
  check(den == 1 && (num == 2 || num == -2), "expected MCSAT value x = +/-2");
  check_code(yices_get_rational64_value(mdl, fx, &num, &den), "model must define f(x)");
  check(den == 1 && num == 7, "expected model value f(x) = 7");
  yices_free_model(mdl);

  yices_free_context(ctx);
}

static void test_division_by_zero_remains_error(void) {
  context_t *ctx;
  term_t r, z, div, f;
  int32_t code;

  ctx = make_cdclt_context("QF_ALIRA");
  r = yices_new_uninterpreted_term(yices_real_type());
  z = yices_rational32(0, 1);
  div = yices_division(r, z);
  f = yices_arith_eq_atom(div, z);

  code = yices_assert_formula(ctx, f);
  check(code < 0, "asserting division-by-zero formula should fail");
  check(yices_error_code() == DIVISION_BY_ZERO, "expected DIVISION_BY_ZERO");

  yices_free_context(ctx);
}

static void test_disabling_required_supplement_is_invalid(void) {
  ctx_config_t *cfg;
  context_t *ctx;

  cfg = yices_new_config();
  check(cfg != NULL, "yices_new_config failed");

  check_code(yices_default_config_for_logic(cfg, "QF_NIA"),
             "default_config_for_logic(QF_NIA) failed");
  check_code(yices_set_config(cfg, "solver-type", "dpllt"),
             "setting solver-type=dpllt failed");
  check_code(yices_set_config(cfg, "mcsat-supplement", "false"),
             "setting mcsat-supplement=false failed");

  ctx = yices_new_context(cfg);
  check(ctx == NULL, "expected invalid config when DPLL(T) QF_NIA disables MCSAT supplement");
  check(yices_error_code() == CTX_INVALID_CONFIG, "expected CTX_INVALID_CONFIG");

  yices_free_config(cfg);
}

static void test_reset_reassert_supplement(void) {
  context_t *ctx;
  term_t x, xx, bad, xeq2, good;
  smt_status_t stat;
  model_t *mdl;

  ctx = make_cdclt_context("QF_UFLIA");
  x = yices_new_uninterpreted_term(yices_int_type());
  xx = yices_mul(x, x);

  bad = yices_arith_eq_atom(xx, yices_int32(2));
  check_code(yices_assert_formula(ctx, bad), "assert x*x=2 before reset failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_UNSAT, "expected UNSAT for integer x*x=2 before reset");

  yices_reset_context(ctx);

  xeq2 = yices_arith_eq_atom(x, yices_int32(2));
  good = yices_arith_eq_atom(xx, yices_int32(4));
  check_code(yices_assert_formula(ctx, xeq2), "assert x=2 after reset failed");
  check_code(yices_assert_formula(ctx, good), "assert x*x=4 after reset failed");
  stat = yices_check_context(ctx, NULL);
  check_status(stat, YICES_STATUS_SAT, "expected SAT after reset/reassert");

  mdl = yices_get_model(ctx, 1);
  check(mdl != NULL, "get_model failed after reset/reassert");
  check(yices_formula_true_in_model(mdl, good) == 1, "model must satisfy x*x=4 after reset");
  yices_free_model(mdl);

  yices_free_context(ctx);
}

int main(void) {
  if (!yices_has_mcsat()) {
    return 1; // skipped
  }

  yices_init();

  test_nla_sat_unsat_and_model();
  test_nla_hidden_product_and_push_pop();
  test_nonconstant_divisor_and_param_modes();
  test_ff_sat_unsat_model_and_assumption_core();
  test_nla_assumption_core();
  test_simplex_relaxation_phase2();
  test_mcsat_model_values_drive_egraph_model();
  test_division_by_zero_remains_error();
  test_disabling_required_supplement_is_invalid();
  test_reset_reassert_supplement();

  yices_exit();
  return 0;
}
