/*
 * Issue #659: interpolation sequences with MCSAT could return an interpolant
 * that mentions a variable that is not shared between the two sides.
 *
 * Formulas (all 32 bits):
 *   A: x2 = 10
 *   B: x2 >= 10 /\ x3 = x2 + 2
 *   C: cond = 0 /\ x3 < 10 /\ x3 >= bit(x3, 0) /\ cond = bit(x3, 0)  (unsat with A, B)
 *
 *   I = itp({A}, {B, C})      must only mention x2
 *   J = itp({B, I}, {C})      must only mention x3 and cond (not x2)
 *
 * The result used to depend on the term numbering (the reporter needed unused
 * integer terms; with exactly one the search did not terminate), so we run the
 * scenario with several numbers of unused terms.
 */

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include <yices.h>

static void fail(const char *msg) {
  yices_print_error(stderr);
  fprintf(stderr, "%s\n", msg);
  exit(2);
}

static context_t *new_context(const char *solver, bool interpolation) {
  ctx_config_t *cfg = yices_new_config();
  context_t *ctx;

  if (yices_set_config(cfg, "solver-type", solver) < 0 ||
      yices_set_config(cfg, "mode", "interactive") < 0 ||
      (interpolation && yices_set_config(cfg, "model-interpolation", "true") < 0)) {
    fail("bad configuration");
  }
  ctx = yices_new_context(cfg);
  yices_free_config(cfg);
  if (ctx == NULL) {
    fail("failed to create context");
  }
  return ctx;
}

static term_t interpolate(uint32_t na, const term_t *a, uint32_t nb, const term_t *b) {
  context_t *ctx_a = new_context("mcsat", true);
  context_t *ctx_b = new_context("mcsat", true);
  interpolation_context_t ictx = {ctx_a, ctx_b, NULL_TERM, NULL};
  term_t result;

  if (yices_assert_formulas(ctx_a, na, a) < 0 || yices_assert_formulas(ctx_b, nb, b) < 0) {
    fail("assert failed");
  }
  if (yices_check_context_with_interpolation(&ictx, NULL, false) != YICES_STATUS_UNSAT) {
    fail("expected unsat");
  }
  result = ictx.interpolant;
  yices_free_context(ctx_b);
  yices_free_context(ctx_a);
  return result;
}

/* true if the conjunction of the formulas is unsat */
static bool is_unsat(uint32_t n, const term_t *f) {
  context_t *ctx = new_context("dpllt", false);
  smt_status_t status;

  if (yices_assert_formulas(ctx, n, f) < 0) {
    fail("assert failed");
  }
  status = yices_check_context(ctx, NULL);
  yices_free_context(ctx);
  return status == YICES_STATUS_UNSAT;
}

/*
 * t does not contain var iff substituting var by a different term of the same type
 * gives back t (terms are hash-consed).
 */
static bool mentions(term_t t, term_t var, term_t other) {
  return yices_subst_term(1, &var, &other, t) != t;
}

static void run(int unused) {
  term_t x2, x3, cond, other, zero, ten, one, two;
  term_t A, B, C, I, J, tmp[3];
  term_t bit0, c1, c2, c3, c4;
  type_t bv32;
  int i;

  yices_init();

  // These are not used by the formulas, but change the term numbering
  for (i = 0; i < unused; i ++) {
    (void) yices_int32(1000 + i);
  }

  bv32 = yices_bv_type(32);
  x2 = yices_new_uninterpreted_term(bv32);
  x3 = yices_new_uninterpreted_term(bv32);
  cond = yices_new_uninterpreted_term(bv32);
  other = yices_new_uninterpreted_term(bv32);
  yices_set_term_name(x2, "x2");
  yices_set_term_name(x3, "x3");
  yices_set_term_name(cond, "cond");
  yices_set_term_name(other, "other");

  zero = yices_bvconst_int32(32, 0);
  one = yices_bvconst_int32(32, 1);
  two = yices_bvconst_int32(32, 2);
  ten = yices_bvconst_int32(32, 10);

  A = yices_bveq_atom(x2, ten);
  B = yices_and2(yices_bvge_atom(x2, ten), yices_bveq_atom(x3, yices_bvadd(x2, two)));

  // bit0 = (bit x3 0) as a bit-vector of size 32
  bit0 = yices_ite(yices_bitextract(x3, 0), one, zero);
  c1 = yices_bveq_atom(cond, zero);
  c2 = yices_bvlt_atom(x3, ten);
  c3 = yices_bvge_atom(x3, bit0);
  c4 = yices_bveq_atom(cond, bit0);
  tmp[0] = c1; tmp[1] = c2; tmp[2] = yices_and2(c3, c4);
  C = yices_and(3, tmp);

  // Sanity: A, B, C are unsat together
  tmp[0] = A; tmp[1] = B; tmp[2] = C;
  if (!is_unsat(3, tmp)) {
    fail("A, B, C should be unsat");
  }

  // I = itp({A}, {B, C})
  tmp[0] = B; tmp[1] = C;
  I = interpolate(1, &A, 2, tmp);

  // I must only mention x2
  if (mentions(I, x3, other) || mentions(I, cond, other)) {
    fail("I mentions a non-shared variable");
  }
  // A => I and I /\ B /\ C unsat
  tmp[0] = A; tmp[1] = yices_not(I);
  if (!is_unsat(2, tmp)) fail("A does not imply I");
  {
    term_t f[3] = {I, B, C};
    if (!is_unsat(3, f)) fail("I /\\ B /\\ C is satisfiable");
  }

  // J = itp({B, I}, {C})
  tmp[0] = B; tmp[1] = I;
  J = interpolate(2, tmp, 1, &C);

  // J must only mention the shared variables x3 and cond, in particular not x2
  if (mentions(J, x2, other)) {
    fail("J mentions x2, which is not shared between {B, I} and {C}");
  }
  // B /\ I => J and J /\ C unsat
  {
    term_t f[3] = {B, I, yices_not(J)};
    if (!is_unsat(3, f)) fail("B /\\ I does not imply J");
  }
  tmp[0] = J; tmp[1] = C;
  if (!is_unsat(2, tmp)) fail("J /\\ C is satisfiable");

  yices_exit();
}

int main(void) {
  int unused;

  for (unused = 0; unused < 4; unused ++) {
    run(unused);
  }
  printf("ok\n");
  return 0;
}
