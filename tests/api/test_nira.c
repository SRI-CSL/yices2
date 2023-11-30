#ifdef NDEBUG
#undef NDEBUG
#endif

#include <stdlib.h>

#include "assert.h"

#include <yices.h>

int main(void)
{
  if (! yices_has_mcsat()) {
    return 1; // skipped
  }
  yices_init();

  ctx_config_t* config = yices_new_config();
  yices_set_config(config, "solver-type", "mcsat");
  context_t* ctx = yices_new_context(config);

  term_t x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "x");

  term_t y = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(y, "y");

  term_t p_x = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(p_x, "p_x");

  term_t p_y = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(p_y, "p_y");

  term_t p_xy = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(p_xy, "p_xy");

  assert(!yices_error_code());

  term_t xy = yices_mul(x, y);

  // assertion

  yices_assert_formula(ctx, yices_arith_eq_atom(x, p_x));
  yices_assert_formula(ctx, yices_arith_gt_atom(p_x, yices_int32(1)));
  yices_assert_formula(ctx, yices_arith_lt_atom(p_x, yices_int32(7)));
  
  yices_assert_formula(ctx, yices_arith_eq_atom(y, p_y));
  yices_assert_formula(ctx, yices_arith_gt_atom(p_y, yices_int32(1)));
  yices_assert_formula(ctx, yices_arith_lt_atom(p_y, yices_int32(7)));
  
  yices_assert_formula(ctx, yices_arith_eq_atom(xy, p_xy));
  yices_assert_formula(ctx, yices_arith_eq_atom(p_xy, yices_int32(7)));

  smt_status_t status;
  status = yices_check_context(ctx, NULL);
  assert(!yices_error_code());

  assert(status == STATUS_UNSAT);

  yices_free_context(ctx);
  yices_exit();

  return 0;
}
