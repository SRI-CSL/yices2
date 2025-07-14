/* Achieves the following additional coverage:
 * terms/rba_buffer_terms.c:rba_buffer_mul_term_power(), case POWER_PRODUCT
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

#include "yices.h"

int main(void) {
    if (!yices_has_mcsat()) {
                return 1; // skipped
    }
    yices_init();

    ctx_config_t* config = yices_new_config();
    yices_default_config_for_logic(config, "QF_NIA");
    context_t* ctx = yices_new_context(config);

    assert(!yices_error_code());

    term_t x = yices_new_uninterpreted_term(yices_int_type());
    yices_set_term_name(x, "x");
    term_t power_term = yices_power(yices_square(x), 2);

    yices_assert_formula(ctx, yices_arith_leq_atom(power_term, x));
    assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
    assert(!yices_error_code());

    yices_free_context(ctx);
    yices_exit();

    return 0;

}
