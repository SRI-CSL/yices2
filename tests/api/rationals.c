/* Achieved the following additional coverage:
 * terms/rationals.c: q_set64() - then branch
 *                  q_smt2_div() - if (q_is_pos(y)) - else branch
 * api/yices_api.c: yices_int64()
 *                  _o_yices_int64()
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

  term_t val = yices_int64(-8);
  val = yices_idiv(val, val);

  yices_assert_formula(ctx, yices_arith_eq_atom(val, yices_int32(1)));
  assert(yices_check_context(ctx, NULL) == SMT_STATUS_SAT);

  assert(!yices_error_code());

  yices_free_context(ctx);
  yices_exit();

  return 0;
}
