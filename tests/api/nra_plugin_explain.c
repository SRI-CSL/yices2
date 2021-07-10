/* Achieves the following additional coverage:
 * mcsat/nra/nra_plugin_explain.c:310-311
 * api/yices_api.c: yices_error_code()
 *          check_square_degree()
 *          check_power_degree()
 *          yices_square()
 *          yices_power()
 *          yices_mul()
 *          yices_sub()
 *          yices_zero()
 *          yices_int32()
 *          _o_yices_int32()
 *          yices_ite()
 *          yices_arith_leq_atom()
 *          _o_yices_arith_leq_atom()
 *          yices_new_context()
 *          yices_check_context() - STATUS_IDLE branch
 */

#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>

#include "yices.h"

term_t arbitrary_expr(void) {
  term_t t1 = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(t1, "x_in");
  term_t t2 = yices_power(t1, 4);
  term_t t3 = yices_arith_leq_atom(t1, yices_zero());
  term_t t4 = yices_ite(t3, t1, yices_zero());
  term_t t5 = yices_abs(t2);
  term_t t6 = yices_sub(t2, t4);
  term_t t7 = yices_square(t6);
  term_t t8 = yices_mul(t5, t7);
  return yices_mul(t4, t8);
}

int main(void) {
  if (! yices_has_mcsat()) {
    return 1; // skipped
  }
  yices_init();

  ctx_config_t* config = yices_new_config();
  yices_default_config_for_logic(config, "QF_NIA");
  context_t* ctx = yices_new_context(config);

  assert(!yices_error_code());

  term_t one = yices_int32(1);

  // Metamorphic variant r_1 should evaluate to 1 by construction
  // Get arbitrary expr in `arbitrary` variable
  term_t arbitrary = arbitrary_expr();
  term_t r_1 = yices_ite(yices_eq(yices_zero(), arbitrary),
    one, yices_idiv(arbitrary, arbitrary));

  term_t f_arr[] = { r_1, one };
  yices_assert_formula(ctx, yices_distinct(2, f_arr));
  assert(yices_check_context(ctx, NULL) == STATUS_UNSAT);
  assert(!yices_error_code());

  yices_free_context(ctx);
  yices_exit();

  return 0;
}
