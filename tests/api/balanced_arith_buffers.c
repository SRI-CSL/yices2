/* Commit ID: a083255e3ee132988baacd7f3f1bc83121a842ef
 *
 * Achieves the following additional coverage:
 * terms/balanced_arith_buffers.c:rba_buffer_square()
 *                                rba_buffer_mul_monarray_power() - 1892,1899,1900,1907-1913,1916
 *       rba_buffer_terms.c:rba_buffer_mul_term_power() - ARITH_POLY case (213-220)
 *       term_manager.c:3487 (mk_arith_mod() special case setting `t = zero_term`)
 * api/context_config:config_set_field() - 350-361,418
 *     yices_api.c:model_of_header()
 *                 free_model_list() - 783-786
 *                 yices_arith_eq_atom()
 *                 _o_yices_arith_eq_atom() - 4319,4320,4323
 *                 yices_set_config(): 8033,8034,8044
 *                 yices_reset_context()
 *                 yices_push() - 8487,8492,8498,8499,8521,8523
 *                 yices_pop() - 8541,8546,8551,8552,8555,8556,8577,8579
 *                 yices_get_bool_value()
 *                 _o_yices_get_bool_value() - 10655,10656,10660,10661,10666,10667,10672,10674
 * model/model_queries.c:47-49
 * utils/string_utils.c:parse_as_keyword()
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

#include "yices.h"

term_t
arbitrary_expr()
{
    term_t t_1 = yices_new_uninterpreted_term(yices_int_type());
    yices_set_term_name(t_1, "x_in");

    term_t t_2 = yices_sub(t_1, yices_int32(1));
    term_t t_3 = yices_power(t_2, 8);
    return t_3;
}

int main(void) {

    if (! yices_has_mcsat()) {
        return 1; // skipped
    }

    yices_init();

    ctx_config_t* config = yices_new_config();
    yices_default_config_for_logic(config, "QF_NIA");
    yices_set_config(config, "mode", "push-pop");
    context_t* ctx = yices_new_context(config);

    assert(!yices_error_code());

    term_t zero = yices_zero();
    term_t one = yices_int32(1);

    // Metamorphic variants r_0 and r_1 both should evaluate to 0 by construction
    // For r_0, the `else` branch is unreachable, but attains additional coverage
    term_t r_0 = yices_ite(yices_true(), yices_zero(), arbitrary_expr());
    term_t r_1 = yices_imod(one, one);

    yices_reset_context(ctx);

    // Equivalence check; we ensure that both r_0 and r_1 are equal to 0, and
    // that a valid model for one satisfies the other
    term_t check_zero_r_0 = yices_arith_eq_atom(zero, r_0);
    term_t check_zero_r_1 = yices_arith_eq_atom(zero, r_1);
    term_t model_val;
    model_t* mdl;

    yices_push(ctx);
    // Check that `r_1 == 0` holds
    yices_assert_formula(ctx, check_zero_r_1);
    smt_status_t stat_1 = yices_check_context(ctx, NULL);
    assert(stat_1 == STATUS_SAT);
    // Check that the model for `r_1 == 0` validates `r_0 == 0`
    mdl = yices_get_model(ctx, 1);
    assert(yices_get_bool_value(mdl, check_zero_r_0, &model_val) == 0);
    assert(model_val);
    yices_pop(ctx);
    assert(!yices_error_code());

    // Similar to above, check `r_0 == 0` holds
    yices_push(ctx);
    yices_assert_formula(ctx, check_zero_r_0);
    smt_status_t stat_2 = yices_check_context(ctx, NULL);
    assert(stat_2 == STATUS_SAT);
    // Model check
    mdl = yices_get_model(ctx, 1);
    assert(yices_get_bool_value(mdl, check_zero_r_1, &model_val) == 0);
    assert(model_val);
    yices_pop(ctx);
    assert(!yices_error_code());

    yices_free_context(ctx);
    yices_exit();

    return 0;
}

