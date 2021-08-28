/* Achieved the following additional coverage:
 * terms/mpq_aux.h: mpq_is_nonpos()
 *       rationals.h: q_is_nonpos()
 *       term_manager.c: mk_arith_opposite()
 *       term_utils.c: arith_term_is_nonpos() - case ARITH_CONSTANT
 */

#ifdef NDEBUG
#undef NDEBUG
#endif
#include "assert.h"

#include "yices.h"

int main(void) {
  if (! yices_has_mcsat()) {
    return 1; // skipped
  }
  yices_init();

  ctx_config_t* config = yices_new_config();
  yices_default_config_for_logic(config, "QF_NIA");
  context_t* ctx = yices_new_context(config);

  assert(!yices_error_code());

  // This value is equivalent to 2 ^ 15
  term_t val = yices_int32(32768);
  val = yices_mul(val, yices_neg(val));
  val = yices_abs(val);

  yices_assert_formula(ctx, yices_arith_eq_atom(val, yices_power(yices_int32(2), 30)));
  assert(yices_check_context(ctx, NULL) == STATUS_SAT);

  assert(!yices_error_code());

  yices_free_context(ctx);
  yices_exit();

  return 0;
}
