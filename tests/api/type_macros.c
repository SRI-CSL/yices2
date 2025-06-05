/* Achieves the following additional coverage:
 * api/yices_api.c:yices_type_variable(),
 *                 yices_type_constructor(),
 *                 yices_type_macro(),
 *                 yices_instance_type(),     
 *                 yices_get_macro_by_name(),
 *                 yices_remove_type_macro_name(),
 *                 yices_delete_type_macro()
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

#include "yices_limits.h"
#include "yices.h"

void check_type_variable(void) 
{
    type_t tv0 = yices_type_variable(0);
    assert(!yices_error_code());

    type_t tv1 = yices_type_variable(1);
    assert(!yices_error_code());

    type_t tv0_1 = yices_type_variable(0);
    assert(tv0 == tv0_1);
    assert(tv0 != tv1);
}

void check_type_constructor(void)
{
    yices_type_constructor("tc0", 0);
    assert(yices_error_code() == POS_INT_REQUIRED);
    yices_clear_error();

    yices_type_constructor("tc1", 1);
    assert(!yices_error_code());

    yices_type_constructor("tc2", TYPE_MACRO_MAX_ARITY+1);
    assert(yices_error_code() == TOO_MANY_MACRO_PARAMS);
    yices_clear_error();

    yices_remove_type_macro_name("tc0");
    yices_remove_type_macro_name("tc1");
    yices_remove_type_macro_name("tc2");
}

void check_type_macro(void)
{
    type_t tv0 = yices_type_variable(0);
    type_t tv1 = yices_type_variable(1);

    type_t tc1 = yices_type_constructor("tc0", 1);
    type_t tc2 = yices_type_constructor("tc1", 2);

    type_t vars_0[1] = { tv0 };
    yices_type_macro("tm0", 1, vars_0, tc1);
    assert(!yices_error_code());

    type_t vars_1[2] = { tv0, tv1 };
    yices_type_macro("tm1", 2, vars_1, tc2);
    assert(!yices_error_code());

    yices_type_macro("tm2", 0, NULL, tv0);
    assert(yices_error_code() == POS_INT_REQUIRED);
    yices_clear_error();

    yices_type_macro("tm3", TYPE_MACRO_MAX_ARITY+1, NULL, tc2);
    assert(yices_error_code() == TOO_MANY_MACRO_PARAMS);
    yices_clear_error();

    yices_type_macro("tm4", 1, vars_0, 1000);
    assert(yices_error_code() == INVALID_TYPE);
    yices_clear_error();

    type_t vars_5[1] = { yices_bool_type() };
    yices_type_macro("tm5", 1, vars_5, tv0);
    assert(yices_error_code() == TYPE_VAR_REQUIRED);
    yices_clear_error();

    type_t vars_6[2] = { tv0, tv0 };
    yices_type_macro("tm6", 2, vars_6, tv0);
    assert(yices_error_code() == DUPLICATE_TYPE_VAR);
    yices_clear_error();

    yices_remove_type_macro_name("tc0");
    yices_remove_type_macro_name("tc1");
    yices_remove_type_macro_name("tm0");
    yices_remove_type_macro_name("tm1");
    yices_remove_type_macro_name("tm2");
    yices_remove_type_macro_name("tm3");
    yices_remove_type_macro_name("tm4");
    yices_remove_type_macro_name("tm5");
    yices_remove_type_macro_name("tm6");
}

void check_yices_instance_type(void)
{
    int32_t tc1 = yices_type_constructor("tc1", 1);
    int32_t tc2 = yices_type_constructor("tc2", 2);

    type_t types_0[1] = { yices_bool_type() };
    yices_instance_type(tc1, 1, types_0);
    assert(!yices_error_code());

    type_t types_1[2] = { yices_bool_type(), yices_bool_type() };
    yices_instance_type(tc2, 2, types_1);
    assert(!yices_error_code());

    type_t tv0 = yices_type_variable(0);
    type_t tv_args[1] = { tv0 };
    int32_t tm0 = yices_type_macro("tm0", 1, tv_args, tv0);
    yices_instance_type(tm0, 1, types_0);
    assert(!yices_error_code());

    yices_instance_type(1000, 1, types_0);
    assert(yices_error_code() == INVALID_MACRO);
    yices_clear_error();

    type_t vars_2[1] = { yices_bool_type() };
    yices_instance_type(tc1, 2, vars_2);
    assert(yices_error_code() == WRONG_NUMBER_OF_ARGUMENTS);
    yices_clear_error();

    type_t vars_3[1] = { 1000 };
    yices_instance_type(tc1, 1, vars_3);
    assert(yices_error_code() == INVALID_TYPE);
    yices_clear_error();

    yices_remove_type_macro_name("tc1");
    yices_remove_type_macro_name("tc2");
    yices_remove_type_macro_name("tm0");
}

void check_yices_macro_names(void)
{
    int32_t tc0 = yices_type_constructor("tc0", 1);

    type_t tv0 = yices_type_variable(0);
    type_t tv_args[1] = { tv0 };
    int32_t tm0 = yices_type_macro("tm0", 1, tv_args, tv0);
    assert(!yices_error_code());

    int32_t tm0_get = yices_get_macro_by_name("tm0");
    assert(tm0_get == tm0 && !yices_error_code());
    int32_t tc0_get = yices_get_macro_by_name("tc0");
    assert(tc0_get == tc0 && !yices_error_code());  

    yices_remove_type_macro_name("tm0");
    assert(yices_get_macro_by_name("tm0") == -1 && !yices_error_code());

    yices_delete_type_macro(tm0);
    type_t types_0[1] = { yices_bool_type() };
    yices_instance_type(tm0, 1, types_0);
    assert(yices_error_code());
    yices_clear_error();

    yices_delete_type_macro(tc0);
    assert(yices_get_macro_by_name("tc0") == -1 && !yices_error_code());
}

int main(void) {
    yices_init();

    check_type_variable();
    check_type_constructor();
    check_type_macro();
    check_yices_instance_type();
    check_yices_macro_names();

    yices_exit();
    return 0;
}
