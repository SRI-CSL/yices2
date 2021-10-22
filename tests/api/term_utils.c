/* Achieves the following additional coverage:
 * api/yices_api.c:yices_arith_geq_atom()
 * terms/term_utils.c:finite_domain_is_nonpos(), exiting via `return false`
 *                    term_has_nonpos_finite_domain()
 *                    arith_term_is_nonpos(), case `ITE_SPECIAL`
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

#include "yices.h"

int main(void) {
    yices_init();

    ctx_config_t* config = yices_new_config();
    yices_default_config_for_logic(config, "QF_LIA");
    context_t* ctx = yices_new_context(config);

    term_t x = yices_new_uninterpreted_term(yices_int_type());
    yices_set_term_name(x, "x");

    term_t one = yices_int32(1);
    term_t ite_term = yices_ite(yices_arith_geq_atom(one, x), yices_int32(-1), one);
    term_t abs_term = yices_abs(ite_term);

    yices_assert_formula(ctx, yices_eq(abs_term, one));
    assert(yices_check_context(ctx, NULL) == STATUS_SAT);
    assert(!yices_error_code());

    yices_free_context(ctx);
    yices_exit();

    return 0;
}
