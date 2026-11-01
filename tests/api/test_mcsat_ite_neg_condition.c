#ifdef NDEBUG
#undef NDEBUG
#endif

/*
 * MCSAT ITE plugin with a negative condition.
 *
 * yices_ite normalizes (ite (not p) x y) to (ite p y x), so this test builds
 * the term with the internal constructor to keep the negative condition.
 * Nonlinear constraints fix x and y, so that the context cannot substitute
 * them into the ITE term and rebuild it.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "api/yices_globals.h"
#include "terms/terms.h"
#include "yices.h"

static term_t make_neg_ite(term_t p, term_t x, term_t y) {
  term_t t = ite_term(__yices_globals.terms, yices_int_type(), opposite_term(p), x, y);
  assert(is_neg_term(ite_term_desc(__yices_globals.terms, t)->arg[0]));
  return t;
}

/* Assert p, x = 1 and y = 2 through nonlinear constraints, and the extra formula f. */
static smt_status_t check(term_t p, term_t x, term_t y, term_t f, context_t** out) {
  ctx_config_t* config = yices_new_config();
  yices_default_config_for_logic(config, "QF_NIA");
  context_t* ctx = yices_new_context(config);
  yices_free_config(config);

  yices_assert_formula(ctx, p);
  yices_assert_formula(ctx, yices_arith_eq_atom(yices_mul(x, x), yices_int32(1)));
  yices_assert_formula(ctx, yices_arith_gt_atom(x, yices_zero()));
  yices_assert_formula(ctx, yices_arith_eq_atom(yices_mul(y, y), yices_int32(4)));
  yices_assert_formula(ctx, yices_arith_gt_atom(y, yices_zero()));
  yices_assert_formula(ctx, f);
  assert(!yices_error_code());

  smt_status_t status = yices_check_context(ctx, NULL);
  *out = ctx;
  return status;
}

int main(void) {
  if (!yices_has_mcsat()) {
    return 0;
  }

  yices_init();

  term_t p = yices_new_uninterpreted_term(yices_bool_type());
  term_t x = yices_new_uninterpreted_term(yices_int_type());
  term_t y = yices_new_uninterpreted_term(yices_int_type());
  term_t t = make_neg_ite(p, x, y);
  context_t* ctx;

  // While the condition c of a registered non-Boolean term t = ite(c, a, b)
  // is false on the trail and the trail does not force t to differ from b,
  // when the solver calls the ITE plugin to propagate, the ITE plugin shall
  // add a trail entry that forces t to equal b.
  // When the solver returns sat, the solver shall return a model in which the
  // value of each non-Boolean ITE term equals the value of the selected branch
  // of that term.
  // Here c = (not p) is false, so t equals y = 2.
  assert(check(p, x, y, yices_arith_gt_atom(t, yices_zero()), &ctx) == YICES_STATUS_SAT);
  model_t* mdl = yices_get_model(ctx, true);
  assert(mdl != NULL);
  assert(yices_formula_true_in_model(mdl, yices_arith_eq_atom(t, yices_int32(2))) == 1);
  yices_free_model(mdl);
  yices_free_context(ctx);

  // If the condition of a registered non-Boolean ITE term t selects a branch
  // and the trail forces t to differ from that branch, then the ITE plugin
  // shall report a conflict whose learned clause is (the negated condition
  // literal) or (t equals that branch).
  // Here t = 1 differs from the selected branch y = 2.
  assert(check(p, x, y, yices_arith_eq_atom(t, yices_int32(1)), &ctx) == YICES_STATUS_UNSAT);
  yices_free_context(ctx);

  yices_exit();
  return 0;
}
