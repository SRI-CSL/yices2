/* Achieved the following additional coverage:
 * mcsat/nra/nra_plugin_explain.c: case where
 *          `lp_assignment_get_value(..)->type != LP_VALUE_NONE && sgn == 0
 *          && cmp < 0` in `lp_projection_map_add()`
 * api/yices_api.c: yices_add(term_t, term_t)
 */

#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>

#include "yices.h"

int main(void) {
  if (! yices_has_mcsat()) {
    return 1; // skipped
  }
  yices_init();

  ctx_config_t* config = yices_new_config();
  yices_default_config_for_logic(config, "QF_NIA");
  context_t* ctx = yices_new_context(config);

  term_t free_v = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(free_v, ("x"));
  assert(!yices_error_code());

  // Produces an obfuscated `1` value term
  term_t generated = yices_ite(yices_eq(free_v, yices_zero()),
                       yices_zero(), yices_imod(yices_zero(), free_v));
  term_t one = yices_ite(yices_arith_eq0_atom(generated),
                 yices_int32(1), yices_idiv(generated, generated));

  term_t check = yices_arith_eq_atom(yices_int32(1), one);
  yices_assert_formula(ctx, check);
  smt_status_t stat = yices_check_context(ctx, NULL);
  assert(stat == SMT_STATUS_SAT);
  model_t* mdl = yices_get_model(ctx, 1);
  term_t val;
  assert(yices_get_bool_value(mdl, check, &val) == 0);
  assert(val);
  assert(!yices_error_code());

  yices_free_context(ctx);
  yices_exit();

  return 0;
}
