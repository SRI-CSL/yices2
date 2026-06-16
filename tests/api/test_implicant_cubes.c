/*
 * Regression tests for yices_implicant_cubes_for_formula.
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>

#include <yices.h>


static context_t *new_context(const char *logic) {
  ctx_config_t *config;
  context_t *ctx;

  config = yices_new_config();
  assert(yices_default_config_for_logic(config, logic) == 0);
  ctx = yices_new_context(config);
  assert(ctx != NULL);
  yices_free_config(config);
  return ctx;
}

static model_t *model_for(const char *logic, term_t f) {
  context_t *ctx;
  smt_status_t status;
  model_t *mdl;

  ctx = new_context(logic);
  assert(yices_assert_formula(ctx, f) == 0);
  status = yices_check_context(ctx, NULL);
  assert(status == YICES_STATUS_SAT);
  mdl = yices_get_model(ctx, true);
  assert(mdl != NULL);
  yices_free_context(ctx);
  return mdl;
}

static smt_status_t check_formula(const char *logic, term_t f) {
  context_t *ctx;
  smt_status_t status;

  ctx = new_context(logic);
  assert(yices_assert_formula(ctx, f) == 0);
  status = yices_check_context(ctx, NULL);
  yices_free_context(ctx);
  return status;
}

static void assert_cube_contract(const char *logic, model_t *mdl, term_t target, term_t cube) {
  term_t witness;

  assert(yices_formula_true_in_model(mdl, cube) == 1);

  witness = yices_and2(cube, yices_not(target));
  assert(witness >= 0);
  if (check_formula(logic, witness) != YICES_STATUS_UNSAT) {
    fprintf(stderr, "cube does not imply target\ncube:\n");
    yices_pp_term(stderr, cube, 120, 1, 0);
    fprintf(stderr, "target:\n");
    yices_pp_term(stderr, target, 120, 1, 0);
    assert(0);
  }
}

static void test_boolean_subset_minimal_cubes(void) {
  type_t bool_type;
  term_t a, b, c, target, model_formula, ab, ac, args[3];
  model_t *mdl;
  term_vector_t cubes;
  uint32_t i;
  term_t bc, not_bc, witness;

  printf("\n=== test_boolean_subset_minimal_cubes ===\n");
  fflush(stdout);

  bool_type = yices_bool_type();
  a = yices_new_uninterpreted_term(bool_type);
  b = yices_new_uninterpreted_term(bool_type);
  c = yices_new_uninterpreted_term(bool_type);
  yices_set_term_name(a, "a");
  yices_set_term_name(b, "b");
  yices_set_term_name(c, "c");

  ab = yices_and2(a, b);
  ac = yices_and2(a, c);
  target = yices_or2(ab, ac);

  args[0] = a;
  args[1] = b;
  args[2] = c;
  model_formula = yices_and(3, args);
  mdl = model_for("QF_UF", model_formula);

  yices_init_term_vector(&cubes);
  assert(yices_implicant_cubes_for_formula(mdl, target, 0, &cubes) == 0);
  printf("cubes: %u\n", cubes.size);
  yices_pp_term_array(stdout, cubes.size, cubes.data, 120, 10, 0, 1);

  assert(cubes.size == 2);
  bc = yices_and2(b, c);
  not_bc = yices_not(bc);
  for (i = 0; i < cubes.size; i++) {
    assert_cube_contract("QF_UF", mdl, target, cubes.data[i]);

    /*
     * A bloated model cube {a,b,c} would imply b /\ c. The strict
     * false-first enumerator must return subset-minimal cubes instead.
     */
    witness = yices_and2(cubes.data[i], not_bc);
    assert(witness >= 0);
    assert(check_formula("QF_UF", witness) == YICES_STATUS_SAT);
  }

  yices_delete_term_vector(&cubes);
  yices_free_model(mdl);
}

static void test_arithmetic_ite_condition_free_cube(void) {
  term_t c, ite, target, model_formula;
  model_t *mdl;
  term_vector_t cubes;

  printf("\n=== test_arithmetic_ite_condition_free_cube ===\n");
  fflush(stdout);

  c = yices_new_uninterpreted_term(yices_bool_type());
  yices_set_term_name(c, "ite_c");
  ite = yices_ite(c, yices_int32(2), yices_int32(3));
  target = yices_arith_lt_atom(ite, yices_int32(4));
  model_formula = yices_and2(c, target);
  mdl = model_for("QF_LRA", model_formula);

  yices_init_term_vector(&cubes);
  assert(yices_implicant_cubes_for_formula(mdl, target, 0, &cubes) == 0);
  printf("cubes: %u\n", cubes.size);
  yices_pp_term_array(stdout, cubes.size, cubes.data, 120, 10, 0, 1);

  assert(cubes.size == 1);
  assert(cubes.data[0] == yices_true());
  assert_cube_contract("QF_LRA", mdl, target, cubes.data[0]);

  yices_delete_term_vector(&cubes);
  yices_free_model(mdl);
}

static void test_forced_last_cube_exhausts(void) {
  type_t bool_type;
  term_t a, b, target, model_formula;
  model_t *mdl;
  term_vector_t cubes;

  printf("\n=== test_forced_last_cube_exhausts ===\n");
  fflush(stdout);

  bool_type = yices_bool_type();
  a = yices_new_uninterpreted_term(bool_type);
  b = yices_new_uninterpreted_term(bool_type);
  yices_set_term_name(a, "forced_a");
  yices_set_term_name(b, "forced_b");

  target = yices_or2(a, b);
  model_formula = yices_and2(a, yices_not(b));
  mdl = model_for("QF_UF", model_formula);

  yices_init_term_vector(&cubes);
  assert(yices_implicant_cubes_for_formula(mdl, target, 0, &cubes) == 0);
  printf("cubes: %u\n", cubes.size);
  yices_pp_term_array(stdout, cubes.size, cubes.data, 120, 10, 0, 1);

  assert(cubes.size == 1);
  assert_cube_contract("QF_UF", mdl, target, cubes.data[0]);

  yices_delete_term_vector(&cubes);
  yices_free_model(mdl);
}

int main(void) {
  yices_init();

  test_boolean_subset_minimal_cubes();
  test_arithmetic_ite_condition_free_cube();
  test_forced_last_cube_exhausts();

  yices_exit();
  return 0;
}
