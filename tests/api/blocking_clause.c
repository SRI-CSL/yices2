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
  yices_set_config(config, "mode", "push-pop");
  context_t* ctx = yices_new_context(config);

  term_t x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "x");
  term_t r_0 = yices_arith_eq_atom(x, yices_int32(0));
  term_t r_1 = yices_arith_eq_atom(x, yices_int32(1));
  
  term_t r_0_or_r_1 = yices_or2(r_0, r_1);
  yices_assert_formula(ctx, r_0_or_r_1);
  assert(yices_check_context(ctx, NULL) == STATUS_SAT);

  yices_assert_blocking_clause(ctx);
  assert(yices_check_context(ctx, NULL) == STATUS_SAT);
  
  yices_assert_blocking_clause(ctx);
  assert(yices_check_context(ctx, NULL) == STATUS_UNSAT);

  assert(!yices_error_code());
  
  yices_free_context(ctx);
  yices_exit();

  return 0;
}
