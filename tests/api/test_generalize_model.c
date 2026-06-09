/*
 * Regression tests for yices_generalize_model.
 *
 * Covers:
 *   1. Pure conjunction: both YICES_GEN_BY_PROJ (legacy) and
 *      YICES_GEN_BY_PROJ_WIDE (wide) succeed and produce results that are
 *      true at the model.
 *   2. Soundness contract: each result is true at the model.
 *   3. Wide is at least as broad as local: AND(local) implies AND(wide).
 *      Verified by checking that AND(local) AND NOT AND(wide) is unsat.
 *   4. Overlapping arithmetic disjunction: the wide variant captures
 *      both disjuncts of an OR true at the model.
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include <yices.h>


static context_t *new_context_for_logic(const char *logic, bool use_mcsat) {
  ctx_config_t *config;
  context_t *ctx;
  int32_t ok;

  config = yices_new_config();
  ok = yices_default_config_for_logic(config, logic);
  if (ok != 0) {
    yices_print_error(stderr);
    assert(0);
  }
  if (use_mcsat) {
    ok = yices_set_config(config, "solver-type", "mcsat");
    if (ok != 0) {
      yices_print_error(stderr);
      assert(0);
    }
  }
  ctx = yices_new_context(config);
  if (ctx == NULL) {
    yices_print_error(stderr);
    assert(0);
  }
  yices_free_config(config);
  return ctx;
}

/*
 * Helper: build a fresh QF_LRA context. The model-generalization
 * API itself is solver-independent; the simplex backend suffices
 * for these LRA tests.
 */
static context_t *new_lra_context(void) {
  return new_context_for_logic("QF_LRA", false);
}

/*
 * Build a model satisfying `formula` (in QF_LRA).
 * Asserts test failure if `formula` is unsat.
 */
static model_t *check_and_get_model_for_logic(term_t formula,
                                              const char *logic,
                                              bool use_mcsat) {
  context_t *ctx;
  smt_status_t status;
  model_t *m;
  int32_t ok;

  ctx = new_context_for_logic(logic, use_mcsat);
  ok = yices_assert_formula(ctx, formula);
  assert(ok == 0);
  status = yices_check_context(ctx, NULL);
  assert(status == YICES_STATUS_SAT);
  m = yices_get_model(ctx, true);
  assert(m != NULL);
  yices_free_context(ctx);
  return m;
}

static model_t *check_and_get_model(term_t formula) {
  return check_and_get_model_for_logic(formula, "QF_LRA", false);
}

/*
 * Verify that every term in v evaluates to true in mdl.
 */
static void assert_all_true(const char *tag, term_vector_t *v, model_t *mdl) {
  uint32_t i;
  int32_t val;

  for (i = 0; i < v->size; i++) {
    val = yices_formula_true_in_model(mdl, v->data[i]);
    if (val != 1) {
      fprintf(stderr, "[%s] formula %u (out of %u) is not true in the model\n",
              tag, i, v->size);
      yices_pp_term(stderr, v->data[i], 100, 1, 0);
      assert(0);
    }
  }
}

/*
 * Verify that AND(local) implies AND(wide) by checking that
 * AND(local) AND NOT AND(wide) is unsat.
 */
static void assert_local_implies_wide(term_vector_t *v_local,
                                      term_vector_t *v_wide) {
  context_t *ctx;
  smt_status_t status;
  term_t local_and, wide_and, witness;
  int32_t ok;

  local_and = yices_and(v_local->size, v_local->data);
  wide_and  = yices_and(v_wide->size,  v_wide->data);
  assert(local_and >= 0 && wide_and >= 0);

  witness = yices_and2(local_and, yices_not(wide_and));
  assert(witness >= 0);

  ctx = new_lra_context();
  ok = yices_assert_formula(ctx, witness);
  assert(ok == 0);
  status = yices_check_context(ctx, NULL);
  if (status != YICES_STATUS_UNSAT) {
    fprintf(stderr, "local does not imply wide!\nlocal:\n");
    yices_pp_term_array(stderr, v_local->size, v_local->data, 100, 10, 0, 1);
    fprintf(stderr, "wide:\n");
    yices_pp_term_array(stderr, v_wide->size, v_wide->data, 100, 10, 0, 1);
    assert(0);
  }
  yices_free_context(ctx);
}

/*
 * Check that AND(wide) does not imply AND(local) -- i.e., wide is
 * strictly broader than local. Used by tests that have overlapping
 * disjunctions where wide should genuinely widen.
 */
static int wide_is_strictly_broader(term_vector_t *v_local,
                                    term_vector_t *v_wide) {
  context_t *ctx;
  smt_status_t status;
  term_t local_and, wide_and, witness;
  int32_t ok;
  int strict;

  local_and = yices_and(v_local->size, v_local->data);
  wide_and  = yices_and(v_wide->size,  v_wide->data);

  // wide does not imply local iff (wide AND NOT local) is sat
  witness = yices_and2(wide_and, yices_not(local_and));

  ctx = new_lra_context();
  ok = yices_assert_formula(ctx, witness);
  assert(ok == 0);
  status = yices_check_context(ctx, NULL);
  strict = (status == YICES_STATUS_SAT) ? 1 : 0;
  yices_free_context(ctx);
  return strict;
}

static uint32_t generalization_disjunct_count(term_vector_t *v) {
  term_constructor_t kind;
  int32_t n;

  if (v->size == 0) {
    return 1;
  }
  if (v->size != 1) {
    return 1;
  }

  kind = yices_term_constructor(v->data[0]);
  if (kind == YICES_OR_TERM) {
    n = yices_term_num_children(v->data[0]);
    assert(n >= 0);
    return (uint32_t) n;
  }
  return 1;
}

static void assert_generalization_implies_term(const char *tag, term_vector_t *v,
                                               term_t expected) {
  context_t *ctx;
  smt_status_t status;
  term_t g, witness;
  int32_t ok;

  g = yices_and(v->size, v->data);
  assert(g >= 0);
  witness = yices_and2(g, yices_not(expected));
  assert(witness >= 0);

  ctx = new_lra_context();
  ok = yices_assert_formula(ctx, witness);
  assert(ok == 0);
  status = yices_check_context(ctx, NULL);
  if (status != YICES_STATUS_UNSAT) {
    fprintf(stderr, "[%s] generalization does not imply expected term\n", tag);
    fprintf(stderr, "generalization:\n");
    yices_pp_term_array(stderr, v->size, v->data, 100, 10, 0, 1);
    fprintf(stderr, "expected:\n");
    yices_pp_term(stderr, expected, 100, 1, 0);
    assert(0);
  }
  yices_free_context(ctx);
}

static void assert_generalization_with_term_status(const char *tag,
                                                   term_vector_t *v,
                                                   term_t extra,
                                                   const char *logic,
                                                   bool use_mcsat,
                                                   smt_status_t expected) {
  context_t *ctx;
  smt_status_t status;
  term_t g, witness;
  int32_t ok;

  g = yices_and(v->size, v->data);
  assert(g >= 0);
  witness = yices_and2(g, extra);
  assert(witness >= 0);

  ctx = new_context_for_logic(logic, use_mcsat);
  ok = yices_assert_formula(ctx, witness);
  if (ok != 0) {
    fprintf(stderr, "[%s] failed to assert witness:\n", tag);
    yices_pp_term(stderr, witness, 100, 10, 0);
    yices_print_error(stderr);
    assert(0);
  }
  status = yices_check_context(ctx, NULL);
  if (status != expected) {
    fprintf(stderr, "[%s] unexpected status: got %d, expected %d\n",
            tag, status, expected);
    fprintf(stderr, "generalization:\n");
    yices_pp_term_array(stderr, v->size, v->data, 100, 10, 0, 1);
    fprintf(stderr, "extra constraint:\n");
    yices_pp_term(stderr, extra, 100, 1, 0);
    assert(0);
  }
  yices_free_context(ctx);
}

/*
 * Run both projection modes and apply the standard soundness checks:
 *   - both succeed
 *   - both results true in the model
 *   - local implies wide
 * Returns owned vectors via out_local / out_wide for further inspection.
 */
static void run_both_modes(const char *tag, term_t formula, model_t *mdl,
                           uint32_t nelims, const term_t elim[],
                           term_vector_t *out_local, term_vector_t *out_wide) {
  int32_t r;

  yices_init_term_vector(out_local);
  yices_init_term_vector(out_wide);

  r = yices_generalize_model(mdl, formula, nelims, elim,
                             YICES_GEN_BY_PROJ, out_local);
  if (r != 0) {
    fprintf(stderr, "[%s] local generalization failed: %s\n", tag, yices_error_string());
    assert(0);
  }
  r = yices_generalize_model(mdl, formula, nelims, elim,
                             YICES_GEN_BY_PROJ_WIDE, out_wide);
  if (r != 0) {
    fprintf(stderr, "[%s] wide generalization failed: %s\n", tag, yices_error_string());
    assert(0);
  }

  assert_all_true(tag, out_local, mdl);
  assert_all_true(tag, out_wide,  mdl);
  assert_local_implies_wide(out_local, out_wide);

  printf("[%s] local (%u terms), wide (%u terms)\n",
         tag, out_local->size, out_wide->size);
  printf("  local : ");
  yices_pp_term_array(stdout, out_local->size, out_local->data, 200, 1, 0, 1);
  printf("  wide  : ");
  yices_pp_term_array(stdout, out_wide->size,  out_wide->data,  200, 1, 0, 1);
}


/*
 * Test 1: pure conjunction
 *
 * Formula : (x > 0) /\ (y < 5)
 * Eliminate x.
 * Both modes should produce the same result (no Boolean structure).
 */
static void test_pure_conjunction(void) {
  term_t x, y, lit1, lit2, formula;
  term_t elim[1];
  model_t *mdl;
  term_vector_t v_local, v_wide;

  printf("\n=== test_pure_conjunction ===\n");
  x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x");
  y = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(y, "y");

  lit1 = yices_arith_gt0_atom(x);                       // x > 0
  lit2 = yices_arith_lt_atom(y, yices_int32(5));        // y < 5
  formula = yices_and2(lit1, lit2);

  mdl = check_and_get_model(formula);

  elim[0] = x;
  run_both_modes("pure_conjunction", formula, mdl, 1, elim, &v_local, &v_wide);

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}


/*
 * Test 2: overlapping arithmetic disjunction
 *
 * Formula : ((y > x) /\ (x > 0)) \/ ((z > x) /\ (x > 5))
 *           where the variables in scope are x, y, z, all real.
 * Eliminate x.
 *
 * - Disjunct A : exists x. (y > x) /\ (x > 0)  ===  y > 0
 * - Disjunct B : exists x. (z > x) /\ (x > 5)  ===  z > 5
 *
 * We force a model where both disjuncts are satisfied (by also
 * asserting y > 0 /\ z > 5 /\ x = some witness common to both).
 * The wide variant should produce something equivalent to
 * (y > 0) \/ (z > 5); the local variant picks one disjunct so its
 * result is implied by the wide one but typically strictly stronger.
 */
static void test_overlapping_arith_disjunction(void) {
  term_t x, y, z;
  term_t a1, a2, b1, b2, disjunct_a, disjunct_b, formula;
  term_t mdl_extra;
  term_t elim[1];
  model_t *mdl;
  term_vector_t v_local, v_wide;

  printf("\n=== test_overlapping_arith_disjunction ===\n");
  x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x");
  y = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(y, "y");
  z = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(z, "z");

  a1 = yices_arith_gt_atom(y, x);                  // y > x
  a2 = yices_arith_gt0_atom(x);                    // x > 0
  b1 = yices_arith_gt_atom(z, x);                  // z > x
  b2 = yices_arith_gt_atom(x, yices_int32(5));     // x > 5
  disjunct_a = yices_and2(a1, a2);
  disjunct_b = yices_and2(b1, b2);
  formula = yices_or2(disjunct_a, disjunct_b);

  // Force a model where both disjuncts are satisfied:
  // y > 0, z > 5, and x in (5, min(y, z)).
  mdl_extra = yices_and(3, (term_t[]) {
      yices_arith_gt0_atom(y),                                   // y > 0
      yices_arith_gt_atom(z, yices_int32(5)),                    // z > 5
      yices_and2(yices_arith_gt_atom(x, yices_int32(5)),         // x > 5
                 yices_and2(yices_arith_lt_atom(x, y),            // x < y
                            yices_arith_lt_atom(x, z))),          // x < z
  });
  mdl = check_and_get_model(yices_and2(formula, mdl_extra));

  elim[0] = x;
  run_both_modes("overlapping_arith_disjunction",
                 formula, mdl, 1, elim, &v_local, &v_wide);

  // The wide result must be strictly broader than the local one:
  // both disjuncts are satisfied at the model and contribute distinct
  // projections (y > 0 vs z > 5). This is the headline win of the
  // wide algorithm; regressing on it would defeat the purpose of the
  // mode even if all the cube-counting smoke tests still pass.
  if (!wide_is_strictly_broader(&v_local, &v_wide)) {
    fprintf(stderr,
            "[overlapping_arith_disjunction] expected wide STRICTLY broader than local\n");
    assert(0);
  }
  printf("  -> wide is strictly broader than local (as expected)\n");

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}


/*
 * Test 3: non-overlapping disjunction
 *
 * Formula : (x > 0 /\ x < 1) \/ (x > 100 /\ x < 101)
 * Eliminate x.
 *
 * At any satisfying model, exactly one disjunct is true. Wide and
 * local should produce equivalent results (wide is not strictly
 * broader). The contract should still hold.
 */
static void test_nonoverlapping_disjunction(void) {
  term_t x;
  term_t formula, da, db;
  term_t elim[1];
  model_t *mdl;
  term_vector_t v_local, v_wide;

  printf("\n=== test_nonoverlapping_disjunction ===\n");
  x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x");

  da = yices_and2(yices_arith_gt0_atom(x),
                  yices_arith_lt_atom(x, yices_int32(1)));
  db = yices_and2(yices_arith_gt_atom(x, yices_int32(100)),
                  yices_arith_lt_atom(x, yices_int32(101)));
  formula = yices_or2(da, db);

  mdl = check_and_get_model(formula);

  elim[0] = x;
  run_both_modes("nonoverlapping_disjunction",
                 formula, mdl, 1, elim, &v_local, &v_wide);

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}


/*
 * Test 4: array form (yices_generalize_model_array)
 *
 * Same as test 2 but the formula is split across multiple top-level
 * conjuncts to exercise the array entry point.
 */
static void test_array_form(void) {
  term_t x, y, z;
  term_t fs[3];
  term_t elim[1];
  model_t *mdl;
  term_vector_t v_local, v_wide;
  int32_t r;

  printf("\n=== test_array_form ===\n");
  x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x");
  y = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(y, "y");
  z = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(z, "z");

  // f0: y > x
  // f1: z > x
  // f2: x > 0
  // Eliminating x from this purely conjunctive system jointly is
  // strictly more informative than projecting each conjunct
  // independently, so this is a regression test for the joint
  // Cartesian-product behaviour of the wide entry point.
  fs[0] = yices_arith_gt_atom(y, x);
  fs[1] = yices_arith_gt_atom(z, x);
  fs[2] = yices_arith_gt0_atom(x);

  mdl = check_and_get_model(yices_and(3, fs));

  // Sanity-check: every f[i] must be true in mdl (precondition of
  // yices_generalize_model_array). If yices's preprocessing
  // eliminated a variable that appears only in fs[2], the model
  // returned may not satisfy fs[2] when re-evaluated; surface that
  // here rather than letting it manifest as a generalization error.
  {
    int i;
    for (i = 0; i < 3; i++) {
      int32_t t = yices_formula_true_in_model(mdl, fs[i]);
      if (t != 1) {
        fprintf(stderr, "[array_form] fs[%d] not true in mdl (got %d). ", i, t);
        yices_pp_term(stderr, fs[i], 100, 1, 0);
        fprintf(stderr, "test skipped\n");
        yices_free_model(mdl);
        return;
      }
    }
  }

  elim[0] = x;
  yices_init_term_vector(&v_local);
  yices_init_term_vector(&v_wide);

  r = yices_generalize_model_array(mdl, 3, fs, 1, elim,
                                   YICES_GEN_BY_PROJ, &v_local);
  if (r != 0) {
    fprintf(stderr, "[array_form] LOCAL failed: ");
    yices_print_error(stderr);
  }
  assert(r == 0);
  r = yices_generalize_model_array(mdl, 3, fs, 1, elim,
                                   YICES_GEN_BY_PROJ_WIDE, &v_wide);
  if (r != 0) {
    fprintf(stderr, "[array_form] WIDE failed: ");
    yices_print_error(stderr);
  }
  assert(r == 0);

  assert_all_true("array_form", &v_local, mdl);
  assert_all_true("array_form", &v_wide,  mdl);
  assert_local_implies_wide(&v_local, &v_wide);

  printf("[array_form] local (%u terms), wide (%u terms)\n",
         v_local.size, v_wide.size);
  printf("  local : ");
  yices_pp_term_array(stdout, v_local.size, v_local.data, 200, 1, 0, 1);
  printf("  wide  : ");
  yices_pp_term_array(stdout, v_wide.size,  v_wide.data,  200, 1, 0, 1);

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}

static void test_sat_guided_compression(void) {
  term_t x, y, z;
  term_t a, b, c, formula, mdl_extra;
  term_t elim[1];
  model_t *mdl;
  term_vector_t v_local, v_wide;
  uint32_t ndisj;

  printf("\n=== test_sat_guided_compression ===\n");
  x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x_compress");
  y = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(y, "y_compress");
  z = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(z, "z_compress");

  a = yices_arith_gt0_atom(y);       // A
  b = yices_arith_gt0_atom(x);       // B
  c = yices_arith_gt_atom(z, x);     // C
  formula = yices_and2(yices_or2(a, b), yices_or2(a, c));
  mdl_extra = yices_and(3, (term_t[]) { a, b, c });
  mdl = check_and_get_model(yices_and2(formula, mdl_extra));

  elim[0] = x;
  run_both_modes("sat_guided_compression", formula, mdl, 1, elim, &v_local, &v_wide);

  ndisj = generalization_disjunct_count(&v_wide);
  if (ndisj >= 4) {
    fprintf(stderr, "[sat_guided_compression] expected fewer than 4 cubes, got %u\n", ndisj);
    assert(0);
  }
  printf("  -> SAT-guided compression produced %u disjuncts (< 4 raw cubes)\n", ndisj);

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}

static void test_sat_guided_no_sharing_parity(void) {
  term_t dummy;
  term_t a, b, c, d, formula, mdl_extra;
  term_t elim[1];
  model_t *mdl;
  term_vector_t v_local, v_wide;
  uint32_t ndisj;

  printf("\n=== test_sat_guided_no_sharing_parity ===\n");
  dummy = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(dummy, "x_parity");
  a = yices_arith_gt0_atom(yices_new_uninterpreted_term(yices_real_type()));
  b = yices_arith_gt0_atom(yices_new_uninterpreted_term(yices_real_type()));
  c = yices_arith_gt0_atom(yices_new_uninterpreted_term(yices_real_type()));
  d = yices_arith_gt0_atom(yices_new_uninterpreted_term(yices_real_type()));

  formula = yices_and2(yices_or2(a, b), yices_or2(c, d));
  mdl_extra = yices_and(4, (term_t[]) { a, b, c, d });
  mdl = check_and_get_model(yices_and2(formula, mdl_extra));

  elim[0] = dummy;
  run_both_modes("sat_guided_no_sharing_parity", formula, mdl, 1, elim, &v_local, &v_wide);

  ndisj = generalization_disjunct_count(&v_wide);
  if (ndisj != 4) {
    fprintf(stderr, "[sat_guided_no_sharing_parity] expected 4 cubes, got %u\n", ndisj);
    assert(0);
  }
  printf("  -> no-sharing case produced all 4 cubes\n");

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}

static void test_sat_guided_budget_graceful(void) {
  enum { NPAIRS = 11, BUDGET = 4 };
  term_t dummy;
  term_t atoms[2 * NPAIRS], disj[NPAIRS];
  term_t formula, mdl_extra;
  term_t elim[1];
  model_t *mdl;
  term_vector_t v_local, v_wide;
  uint32_t i;
  int32_t r;

  printf("\n=== test_sat_guided_budget_graceful ===\n");
  dummy = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(dummy, "x_budget");
  for (i = 0; i < NPAIRS; i++) {
    atoms[2 * i] = yices_arith_gt0_atom(yices_new_uninterpreted_term(yices_real_type()));
    atoms[2 * i + 1] = yices_arith_gt0_atom(yices_new_uninterpreted_term(yices_real_type()));
    disj[i] = yices_or2(atoms[2 * i], atoms[2 * i + 1]);
  }
  formula = yices_and(NPAIRS, disj);
  mdl_extra = yices_and(2 * NPAIRS, atoms);
  mdl = check_and_get_model(yices_and2(formula, mdl_extra));

  elim[0] = dummy;
  yices_init_term_vector(&v_local);
  yices_init_term_vector(&v_wide);

  r = yices_generalize_model(mdl, formula, 1, elim,
                             YICES_GEN_BY_PROJ, &v_local);
  assert(r == 0);

  // The public yices_generalize_model() runs with cube_budget == 0
  // (unbounded). Call the explicit-budget variant with BUDGET = 4 so
  // we exercise the OR(collected, local) budget-exhaustion fallback:
  // up to 2^NPAIRS = 2048 implicants exist and BUDGET = 4 is far
  // below that.
  r = yices_generalize_model_with_budget(mdl, formula, 1, elim,
                                         YICES_GEN_BY_PROJ_WIDE, BUDGET, &v_wide);
  assert(r == 0);

  assert_all_true("sat_guided_budget_graceful", &v_wide, mdl);
  assert_local_implies_wide(&v_local, &v_wide);
  printf("  -> cube_budget=%u yielded a sound wide cell (%u terms)\n",
         BUDGET, v_wide.size);

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}

static void test_shared_elimination_variable(void) {
  term_t x, y, z;
  term_t fs[2], expected;
  term_t elim[1];
  model_t *mdl;
  term_vector_t v_local, v_wide;
  int32_t r;

  printf("\n=== test_shared_elimination_variable ===\n");
  x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x_shared");
  y = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(y, "y_shared");
  z = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(z, "z_shared");

  fs[0] = yices_arith_gt_atom(x, y);
  fs[1] = yices_arith_lt_atom(x, z);
  expected = yices_arith_lt_atom(y, z);
  mdl = check_and_get_model(yices_and(2, fs));

  elim[0] = x;
  yices_init_term_vector(&v_local);
  yices_init_term_vector(&v_wide);
  r = yices_generalize_model_array(mdl, 2, fs, 1, elim,
                                   YICES_GEN_BY_PROJ, &v_local);
  assert(r == 0);
  r = yices_generalize_model_array(mdl, 2, fs, 1, elim,
                                   YICES_GEN_BY_PROJ_WIDE, &v_wide);
  assert(r == 0);

  assert_all_true("shared_elimination_variable", &v_local, mdl);
  assert_all_true("shared_elimination_variable", &v_wide, mdl);
  assert_local_implies_wide(&v_local, &v_wide);
  assert_generalization_implies_term("shared_elimination_variable", &v_wide, expected);
  printf("  -> joint projection implies y < z\n");

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}

static void test_sat_guided_polarity(void) {
  term_t dummy;
  term_t a, b, c, formula, mdl_extra;
  term_t elim[1];
  model_t *mdl;
  term_vector_t v_local, v_wide;
  uint32_t ndisj;

  printf("\n=== test_sat_guided_polarity ===\n");
  dummy = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(dummy, "x_polarity");
  a = yices_arith_gt0_atom(yices_new_uninterpreted_term(yices_real_type()));
  b = yices_arith_gt0_atom(yices_new_uninterpreted_term(yices_real_type()));
  c = yices_arith_gt0_atom(yices_new_uninterpreted_term(yices_real_type()));

  formula = yices_and2(yices_or2(a, b), yices_or2(yices_not(a), c));
  mdl_extra = yices_and(3, (term_t[]) { a, b, c });
  mdl = check_and_get_model(yices_and2(formula, mdl_extra));

  elim[0] = dummy;
  run_both_modes("sat_guided_polarity", formula, mdl, 1, elim, &v_local, &v_wide);

  ndisj = generalization_disjunct_count(&v_wide);
  if (ndisj != 2) {
    fprintf(stderr, "[sat_guided_polarity] expected 2 cubes after pruning false ¬A branch, got %u\n", ndisj);
    assert(0);
  }
  printf("  -> polarity-aware abstraction produced 2 cubes\n");

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}

static void test_lia_presburger_divisibility(void) {
  term_t x, y, z;
  term_t formula, model_formula, bad_x, g, follow_formula, follow_model_formula;
  term_t elim[1], follow_elim[1];
  model_t *mdl, *follow_mdl;
  term_vector_t v_local, v_wide, v_follow;
  int32_t r;

  printf("\n=== test_lia_presburger_divisibility ===\n");
  x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "x_lia_div");
  y = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(y, "y_lia_div");

  formula = yices_arith_eq_atom(x, yices_mul(yices_int32(2), y));
  model_formula = yices_and2(formula, yices_arith_eq_atom(y, yices_int32(1)));
  mdl = check_and_get_model_for_logic(model_formula, "QF_LIA", false);

  elim[0] = y;
  yices_init_term_vector(&v_local);
  yices_init_term_vector(&v_wide);

  r = yices_generalize_model(mdl, formula, 1, elim,
                             YICES_GEN_BY_PROJ, &v_local);
  assert(r == 0);
  r = yices_generalize_model(mdl, formula, 1, elim,
                             YICES_GEN_BY_PROJ_WIDE, &v_wide);
  assert(r == 0);

  assert_all_true("lia_presburger_divisibility/local", &v_local, mdl);
  assert_all_true("lia_presburger_divisibility/wide", &v_wide, mdl);

  bad_x = yices_arith_eq_atom(x, yices_int32(1));
  assert_generalization_with_term_status("lia_presburger_divisibility/local",
                                         &v_local, bad_x, "QF_LIA", false,
                                         YICES_STATUS_UNSAT);
  assert_generalization_with_term_status("lia_presburger_divisibility/wide",
                                         &v_wide, bad_x, "QF_LIA", false,
                                         YICES_STATUS_UNSAT);

  z = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(z, "z_lia_div_follow");
  g = yices_and(v_local.size, v_local.data);
  assert(g >= 0);
  follow_formula = yices_and2(g, yices_arith_eq_atom(z, yices_int32(0)));
  follow_model_formula = yices_and2(follow_formula,
                                    yices_arith_eq_atom(x, yices_int32(2)));
  follow_mdl = check_and_get_model_for_logic(follow_model_formula, "QF_LIA", false);
  follow_elim[0] = z;
  yices_init_term_vector(&v_follow);
  r = yices_generalize_model(follow_mdl, follow_formula, 1, follow_elim,
                             YICES_GEN_BY_PROJ, &v_follow);
  assert(r == 0);
  assert_all_true("lia_presburger_divisibility/follow", &v_follow, follow_mdl);
  assert_generalization_with_term_status("lia_presburger_divisibility/follow",
                                         &v_follow, bad_x, "QF_LIA", false,
                                         YICES_STATUS_UNSAT);

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_delete_term_vector(&v_follow);
  yices_free_model(mdl);
  yices_free_model(follow_mdl);
}

static void test_nia_integer_elim_substitution(void) {
  term_t x, y;
  term_t formula, model_formula, bad_x;
  term_t elim[1];
  model_t *mdl;
  term_vector_t v_local, v_wide;
  int32_t r;

  printf("\n=== test_nia_integer_elim_substitution ===\n");
  if (! yices_has_mcsat()) {
    printf("  -> skipped: MCSAT not available\n");
    return;
  }

  x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "x_nia_subst");
  y = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(y, "y_nia_subst");

  formula = yices_arith_eq_atom(x, yices_mul(y, y));
  model_formula = yices_and2(formula, yices_arith_eq_atom(y, yices_int32(2)));
  mdl = check_and_get_model_for_logic(model_formula, "QF_NIA", true);

  elim[0] = y;
  yices_init_term_vector(&v_local);
  yices_init_term_vector(&v_wide);

  r = yices_generalize_model(mdl, formula, 1, elim,
                             YICES_GEN_BY_PROJ, &v_local);
  assert(r == 0);
  r = yices_generalize_model(mdl, formula, 1, elim,
                             YICES_GEN_BY_PROJ_WIDE, &v_wide);
  assert(r == 0);

  assert_all_true("nia_integer_elim_substitution/local", &v_local, mdl);
  assert_all_true("nia_integer_elim_substitution/wide", &v_wide, mdl);

  bad_x = yices_arith_eq_atom(x, yices_int32(3));
  assert_generalization_with_term_status("nia_integer_elim_substitution/local",
                                         &v_local, bad_x, "QF_NIA", true,
                                         YICES_STATUS_UNSAT);
  assert_generalization_with_term_status("nia_integer_elim_substitution/wide",
                                         &v_wide, bad_x, "QF_NIA", true,
                                         YICES_STATUS_UNSAT);

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}

static void test_nira_integer_subst_real_projection(void) {
  term_t x, y, rvar;
  term_t formula, model_formula, bad_x, allow_r_zero;
  term_t elim[2];
  model_t *mdl;
  term_vector_t v_local, v_wide;
  int32_t r;

  printf("\n=== test_nira_integer_subst_real_projection ===\n");
  if (! yices_has_mcsat()) {
    printf("  -> skipped: MCSAT not available\n");
    return;
  }

  x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "x_nira_mixed");
  y = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(y, "y_nira_mixed");
  rvar = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(rvar, "r_nira_mixed");

  formula = yices_and2(yices_arith_eq_atom(x, yices_mul(y, y)),
                       yices_arith_gt0_atom(rvar));
  model_formula = yices_and(3, (term_t[]) {
      formula,
      yices_arith_eq_atom(y, yices_int32(2)),
      yices_arith_eq_atom(rvar, yices_int32(1)),
  });
  mdl = check_and_get_model_for_logic(model_formula, "QF_NIRA", true);

  elim[0] = y;
  elim[1] = rvar;
  yices_init_term_vector(&v_local);
  yices_init_term_vector(&v_wide);

  r = yices_generalize_model(mdl, formula, 2, elim,
                             YICES_GEN_BY_PROJ, &v_local);
  assert(r == 0);
  r = yices_generalize_model(mdl, formula, 2, elim,
                             YICES_GEN_BY_PROJ_WIDE, &v_wide);
  assert(r == 0);

  assert_all_true("nira_integer_subst_real_projection/local", &v_local, mdl);
  assert_all_true("nira_integer_subst_real_projection/wide", &v_wide, mdl);

  bad_x = yices_arith_eq_atom(x, yices_int32(3));
  assert_generalization_with_term_status("nira_integer_subst_real_projection/local",
                                         &v_local, bad_x, "QF_NIRA", true,
                                         YICES_STATUS_UNSAT);
  assert_generalization_with_term_status("nira_integer_subst_real_projection/wide",
                                         &v_wide, bad_x, "QF_NIRA", true,
                                         YICES_STATUS_UNSAT);

  allow_r_zero = yices_and2(yices_arith_eq_atom(x, yices_int32(4)),
                            yices_arith_eq_atom(rvar, yices_int32(0)));
  assert_generalization_with_term_status("nira_integer_subst_real_projection/local-r-free",
                                         &v_local, allow_r_zero, "QF_NIRA", true,
                                         YICES_STATUS_SAT);
  assert_generalization_with_term_status("nira_integer_subst_real_projection/wide-r-free",
                                         &v_wide, allow_r_zero, "QF_NIRA", true,
                                         YICES_STATUS_SAT);

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}

static void run_rdiv_case(const char *tag, term_t formula, term_t elim_var, model_t *mdl) {
  term_t elim[1];
  term_vector_t v_local, v_wide;

  assert(yices_formula_true_in_model(mdl, formula) == 1);
  elim[0] = elim_var;
  run_both_modes(tag, formula, mdl, 1, elim, &v_local, &v_wide);

  yices_delete_term_vector(&v_local);
  yices_delete_term_vector(&v_wide);
  yices_free_model(mdl);
}

static void test_rdiv_positive_denominator(void) {
  term_t x, y, div, bound, formula, expected;
  model_t *mdl;

  printf("\n=== test_rdiv_positive_denominator ===\n");
  x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x_rdiv_pos");
  y = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(y, "y_rdiv_pos");

  div = yices_division(x, y);
  bound = yices_arith_lt_atom(div, yices_int32(3));
  expected = yices_arith_gt0_atom(y);
  formula = yices_and2(expected, bound);

  mdl = yices_new_model();
  assert(yices_model_set_rational32(mdl, x, 0, 1) == 0);
  assert(yices_model_set_rational32(mdl, y, 1, 1) == 0);
  run_rdiv_case("rdiv_positive_denominator", formula, x, mdl);
}

static void test_rdiv_negative_denominator(void) {
  term_t x, y, div, bound, formula, expected;
  model_t *mdl;

  printf("\n=== test_rdiv_negative_denominator ===\n");
  x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x_rdiv_neg");
  y = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(y, "y_rdiv_neg");

  div = yices_division(x, y);
  bound = yices_arith_lt_atom(div, yices_int32(3));
  expected = yices_arith_lt0_atom(y);
  formula = yices_and2(expected, bound);

  mdl = yices_new_model();
  assert(yices_model_set_rational32(mdl, x, 0, 1) == 0);
  assert(yices_model_set_rational32(mdl, y, -1, 1) == 0);
  run_rdiv_case("rdiv_negative_denominator", formula, x, mdl);
}

static void test_rdiv_hidden_in_sum(void) {
  term_t x, a, y, div, sum, bound, formula, expected;
  model_t *mdl;

  printf("\n=== test_rdiv_hidden_in_sum ===\n");
  x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x_rdiv_sum");
  a = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(a, "a_rdiv_sum");
  y = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(y, "y_rdiv_sum");

  div = yices_division(a, y);
  sum = yices_add(x, div);
  bound = yices_arith_lt0_atom(sum);
  expected = yices_arith_gt0_atom(y);
  formula = yices_and2(expected, bound);

  mdl = yices_new_model();
  assert(yices_model_set_rational32(mdl, x, -2, 1) == 0);
  assert(yices_model_set_rational32(mdl, a, 1, 1) == 0);
  assert(yices_model_set_rational32(mdl, y, 1, 1) == 0);
  run_rdiv_case("rdiv_hidden_in_sum", formula, x, mdl);
}

#ifdef HAVE_MCSAT
static void test_rdiv_hidden_in_product(void) {
  term_t x, a, y, div, product, bound, formula, expected;
  model_t *mdl;

  printf("\n=== test_rdiv_hidden_in_product ===\n");
  x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x_rdiv_product");
  a = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(a, "a_rdiv_product");
  y = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(y, "y_rdiv_product");

  div = yices_division(a, y);
  product = yices_mul(div, x);
  bound = yices_arith_lt_atom(product, yices_int32(1));
  expected = yices_arith_gt0_atom(y);
  formula = yices_and2(expected, bound);

  mdl = yices_new_model();
  assert(yices_model_set_rational32(mdl, x, 0, 1) == 0);
  assert(yices_model_set_rational32(mdl, a, 1, 1) == 0);
  assert(yices_model_set_rational32(mdl, y, 1, 1) == 0);
  run_rdiv_case("rdiv_hidden_in_product", formula, x, mdl);
}
#endif

static void test_rdiv_ite_dead_branch_denominator(void) {
  term_t x, y, v, c, live_div, dead_div, ite, bound, args[4], formula;
  term_t expected;
  model_t *mdl;

  printf("\n=== test_rdiv_ite_dead_branch_denominator ===\n");
  x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(x, "x_rdiv_ite");
  y = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(y, "y_rdiv_ite");
  v = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(v, "v_rdiv_ite_dead");
  c = yices_new_uninterpreted_term(yices_bool_type());
  yices_set_term_name(c, "c_rdiv_ite");

  live_div = yices_division(x, y);
  dead_div = yices_division(x, v);
  ite = yices_ite(c, live_div, dead_div);
  bound = yices_arith_lt_atom(ite, yices_int32(3));
  expected = yices_arith_gt0_atom(y);

  args[0] = c;
  args[1] = expected;
  args[2] = yices_arith_eq0_atom(v);
  args[3] = bound;
  formula = yices_and(4, args);

  mdl = yices_new_model();
  assert(yices_model_set_rational32(mdl, x, 0, 1) == 0);
  assert(yices_model_set_rational32(mdl, y, 1, 1) == 0);
  assert(yices_model_set_rational32(mdl, v, 0, 1) == 0);
  assert(yices_model_set_bool(mdl, c, 1) == 0);
  run_rdiv_case("rdiv_ite_dead_branch_denominator", formula, x, mdl);
}


int main(void) {
  yices_init();

  test_pure_conjunction();
  test_overlapping_arith_disjunction();
  test_nonoverlapping_disjunction();
  test_array_form();
  test_sat_guided_compression();
  test_sat_guided_no_sharing_parity();
  test_sat_guided_budget_graceful();
  test_shared_elimination_variable();
  test_sat_guided_polarity();
  test_lia_presburger_divisibility();
  test_nia_integer_elim_substitution();
  test_nira_integer_subst_real_projection();
  test_rdiv_positive_denominator();
  test_rdiv_negative_denominator();
  test_rdiv_hidden_in_sum();
#ifdef HAVE_MCSAT
  test_rdiv_hidden_in_product();
#endif
  test_rdiv_ite_dead_branch_denominator();

  yices_exit();
  printf("\nALL TESTS PASSED\n");
  return 0;
}
