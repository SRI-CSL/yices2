/* Achieves the following additional coverage:
 * mcsat/preprocessor.c: function `preprocessor_build_model()`, `if` branch
 *                       when `eq_desc->arity > 1` holds
 */


#ifdef NDEBUG
#undef NDEBUG
#endif

#include "assert.h"

#include "yices.h"

int main(void)
{
  if (! yices_has_mcsat()) {
    return 1; // skipped
  }
  yices_init();

  ctx_config_t* config = yices_new_config();
  yices_default_config_for_logic(config, "QF_NIA");
  context_t* ctx = yices_new_context(config);

  term_t x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "x");

  assert(!yices_error_code());

  term_t check_eq_zero = yices_arith_eq_atom(yices_zero(), yices_add(x, yices_int32(1)));
  yices_assert_formula(ctx, check_eq_zero);
  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  model_t* mdl = yices_get_model(ctx, 1);
  term_t check_model;
  assert(yices_get_bool_value(mdl, check_eq_zero, &check_model) == 0);
  assert(check_model);

  assert(!yices_error_code());

  yices_free_context(ctx);
  yices_exit();

  return 0;
}
