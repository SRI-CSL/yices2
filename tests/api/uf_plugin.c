/* Additional coverage achieved:
 * mcsat/uf/uf_plugin.c: `case ARITH_IDIV` in `get_function_application_type()`
 *                       in `uf_plugin_build_model`:
 *                          `case ARITH_IDIV` if `prev_app_term != NULL_TERM`
 *                          `case ARITH_MOD`  if `app_terms.size() > 0 && ..`
 * api/yices_api.c: `yices_arith_eq0_atom(term_t)
 * model/concrete_values.c: `vtbl_set_zero_idiv()`
 *                          `vtbl_set_zero_mod()`
 */

#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>

#include "yices.h"

term_t arbitrary_expr(void) {
  term_t x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "x");

  term_t t1 =
      yices_ite(yices_eq(x, yices_zero()), yices_zero(), yices_int32(-1));
  term_t t2 = yices_sub(x, t1);
  term_t t3 = yices_add(x, t1);
  return yices_mul(yices_square(t2), t3);
}

term_t generate_one(void) {
  term_t arbitrary = arbitrary_expr();

  term_t zero = yices_zero();
  term_t alternate_zero =
    yices_ite(yices_eq(arbitrary, zero),
      zero, yices_idiv(zero, arbitrary));
  term_t alternate_one = yices_ite(yices_eq(arbitrary, zero), arbitrary,
                           yices_idiv(arbitrary, arbitrary));
  return yices_ite(yices_eq(alternate_zero, arbitrary),
           yices_int32(1), alternate_one);
}

int main(void) {
  if (! yices_has_mcsat()) {
    return 1; // skipped
  }
  yices_init();

  ctx_config_t* config = yices_new_config();
  yices_default_config_for_logic(config, "QF_NIA");
  context_t* ctx = yices_new_context(config);

  term_t one = generate_one();

  yices_assert_formula(ctx, yices_arith_eq_atom(yices_zero(), one));
  assert(yices_check_context(ctx, NULL) == YICES_STATUS_UNSAT);
  assert(!yices_error_code());

  yices_free_context(ctx);
  yices_exit();

  return 0;
}
