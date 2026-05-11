#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdbool.h>

#include <yices.h>


static context_t *new_fw_context(const char *solver, const char *fragment, bool with_bv) {
  ctx_config_t *config;
  context_t *ctx;

  config = yices_new_config();
  assert(config != NULL);

  assert(yices_set_config(config, "mode", "one-shot") == 0);
  assert(yices_set_config(config, "array-solver", "none") == 0);
  if (!with_bv) {
    assert(yices_set_config(config, "bv-solver", "none") == 0);
  }
  assert(yices_set_config(config, "arith-fragment", fragment) == 0);
  assert(yices_set_config(config, "arith-solver", solver) == 0);

  ctx = yices_new_context(config);
  assert(ctx != NULL);

  yices_free_config(config);
  return ctx;
}


static context_t *new_fw_logic_context(const char *logic, const char *solver) {
  ctx_config_t *config;
  context_t *ctx;

  config = yices_new_config();
  assert(config != NULL);

  assert(yices_default_config_for_logic(config, logic) == 0);
  assert(yices_set_config(config, "mode", "one-shot") == 0);
  assert(yices_set_config(config, "arith-solver", solver) == 0);

  ctx = yices_new_context(config);
  assert(ctx != NULL);

  yices_free_config(config);
  return ctx;
}


static void expect_status(context_t *ctx, smt_status_t expected) {
  smt_status_t stat;

  stat = yices_check_context(ctx, NULL);
  assert(stat == expected);
  assert(yices_error_code() == YICES_NO_ERROR);
}


static void assert_formula_true_in_context_model(context_t *ctx, term_t f) {
  model_t *mdl;

  mdl = yices_get_model(ctx, 1);
  assert(mdl != NULL);
  assert(yices_formula_true_in_model(mdl, f) == 1);
  yices_free_model(mdl);
}


static term_t idl_leq(term_t x, term_t y, int32_t c) {
  return yices_arith_leq_atom(yices_sub(x, y), yices_int32(c));
}


static term_t rdl_leq(term_t x, term_t y, const char *c) {
  return yices_arith_leq_atom(yices_sub(x, y), yices_parse_rational(c));
}


static void check_ifw_logic_config_override(void) {
  context_t *ctx;
  term_t x, y;

  ctx = new_fw_logic_context("QF_UFIDL", "ifw");
  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());

  assert(yices_assert_formula(ctx, yices_eq(x, y)) == 0);
  assert(yices_assert_formula(ctx, idl_leq(x, y, -1)) == 0);
  expect_status(ctx, YICES_STATUS_UNSAT);

  yices_free_context(ctx);
}


static void check_rfw_logic_config_override(void) {
  context_t *ctx;
  term_t x, y;

  ctx = new_fw_logic_context("QF_UFRDL", "rfw");
  x = yices_new_uninterpreted_term(yices_real_type());
  y = yices_new_uninterpreted_term(yices_real_type());

  assert(yices_assert_formula(ctx, yices_eq(x, y)) == 0);
  assert(yices_assert_formula(ctx, rdl_leq(x, y, "-1/2")) == 0);
  expect_status(ctx, YICES_STATUS_UNSAT);

  yices_free_context(ctx);
}


static void check_ifw_sat_atom_disjunction(void) {
  context_t *ctx;
  term_t x, y, a, b;

  ctx = new_fw_context("ifw", "IDL", false);
  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  a = idl_leq(x, y, 2);
  b = idl_leq(y, x, 0);

  assert(yices_assert_formula(ctx, yices_or2(a, b)) == 0);
  expect_status(ctx, YICES_STATUS_SAT);

  yices_free_context(ctx);
}


static void check_rfw_sat_atom_disjunction(void) {
  context_t *ctx;
  term_t x, y, a, b;

  ctx = new_fw_context("rfw", "RDL", false);
  x = yices_new_uninterpreted_term(yices_real_type());
  y = yices_new_uninterpreted_term(yices_real_type());
  a = rdl_leq(x, y, "3/2");
  b = rdl_leq(y, x, "0");

  assert(yices_assert_formula(ctx, yices_or2(a, b)) == 0);
  expect_status(ctx, YICES_STATUS_SAT);

  yices_free_context(ctx);
}


static void check_ifw_guarded_atom(void) {
  context_t *ctx;
  term_t guard, x, y, a;

  ctx = new_fw_context("ifw", "IDL", false);
  guard = yices_new_uninterpreted_term(yices_bool_type());
  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  a = idl_leq(x, y, 0);

  assert(yices_assert_formula(ctx, guard) == 0);
  assert(yices_assert_formula(ctx, yices_implies(guard, a)) == 0);
  expect_status(ctx, YICES_STATUS_SAT);

  yices_free_context(ctx);
}


static void check_ifw_disequality_interface_lemma(void) {
  context_t *ctx;
  term_t x, y, diseq;

  ctx = new_fw_context("ifw", "IDL", false);
  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  diseq = yices_neq(x, y);

  assert(yices_assert_formula(ctx, diseq) == 0);
  assert(yices_assert_formula(ctx, idl_leq(x, y, 1)) == 0);
  assert(yices_assert_formula(ctx, idl_leq(y, x, 1)) == 0);
  expect_status(ctx, YICES_STATUS_SAT);
  assert_formula_true_in_context_model(ctx, diseq);

  yices_free_context(ctx);
}


static void check_ifw_egraph_eq_conflict(void) {
  context_t *ctx;
  term_t x, y;

  ctx = new_fw_context("ifw", "IDL", false);
  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());

  assert(yices_assert_formula(ctx, yices_eq(x, y)) == 0);
  assert(yices_assert_formula(ctx, idl_leq(x, y, -1)) == 0);
  expect_status(ctx, YICES_STATUS_UNSAT);

  yices_free_context(ctx);
}


static void check_rfw_egraph_eq_conflict(void) {
  context_t *ctx;
  term_t x, y;

  ctx = new_fw_context("rfw", "RDL", false);
  x = yices_new_uninterpreted_term(yices_real_type());
  y = yices_new_uninterpreted_term(yices_real_type());

  assert(yices_assert_formula(ctx, yices_eq(x, y)) == 0);
  assert(yices_assert_formula(ctx, rdl_leq(x, y, "-1/2")) == 0);
  expect_status(ctx, YICES_STATUS_UNSAT);

  yices_free_context(ctx);
}


static void check_ifw_egraph_eq_sat(void) {
  context_t *ctx;
  term_t x, y;

  ctx = new_fw_context("ifw", "IDL", false);
  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());

  assert(yices_assert_formula(ctx, yices_eq(x, y)) == 0);
  assert(yices_assert_formula(ctx, idl_leq(x, y, 0)) == 0);
  assert(yices_assert_formula(ctx, idl_leq(y, x, 0)) == 0);
  expect_status(ctx, YICES_STATUS_SAT);

  yices_free_context(ctx);
}


static void check_bv_ifw_guarded_eq_conflict(void) {
  context_t *ctx;
  type_t bv8;
  term_t b, guard, x, y;

  ctx = new_fw_context("ifw", "IDL", true);
  bv8 = yices_bv_type(8);
  b = yices_new_uninterpreted_term(bv8);
  guard = yices_bveq_atom(b, yices_bvconst_uint32(8, 1));
  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());

  assert(yices_assert_formula(ctx, guard) == 0);
  assert(yices_assert_formula(ctx, yices_implies(guard, yices_eq(x, y))) == 0);
  assert(yices_assert_formula(ctx, idl_leq(x, y, -1)) == 0);
  expect_status(ctx, YICES_STATUS_UNSAT);

  yices_free_context(ctx);
}


int main(void) {
  yices_init();

  check_ifw_logic_config_override();
  check_rfw_logic_config_override();
  check_ifw_sat_atom_disjunction();
  check_rfw_sat_atom_disjunction();
  check_ifw_guarded_atom();
  check_ifw_disequality_interface_lemma();
  check_ifw_egraph_eq_conflict();
  check_ifw_egraph_eq_sat();
  check_rfw_egraph_eq_conflict();
  check_bv_ifw_guarded_eq_conflict();

  yices_exit();
  return 0;
}
