/* Achieves the following additional coverage:
 * model/model_eval.c: function `eval_arith_idiv`, `if` branch when
 *                     `object_is_rational(eval->vtbl, v1) && [..]` holds
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include "assert.h"

#include "yices.h"

int main(void)
{
  yices_init();

  ctx_config_t* config = yices_new_config();
  yices_default_config_for_logic(config, "QF_LIA");
  context_t* ctx = yices_new_context(config);

  term_t x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "x");
  term_t r_1 = yices_idiv(x, yices_int32(2));

  term_t check_zero_t1 = yices_arith_eq_atom(yices_zero(), r_1);
  yices_assert_formula(ctx, check_zero_t1);
  assert(yices_check_context(ctx, NULL) == STATUS_SAT);
  model_t* mdl = yices_get_model(ctx, 1);
  term_t check_mdl;
  assert(yices_get_bool_value(mdl, check_zero_t1, &check_mdl) == 0);
  assert(check_mdl);

  assert(!yices_error_code());

  yices_free_context(ctx);
  yices_exit();

  return 0;
}
