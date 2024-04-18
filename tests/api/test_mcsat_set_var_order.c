#ifdef NDEBUG
#undef NDEBUG
#endif

#include <stdlib.h>

#include "assert.h"

#include <yices.h>

void check_fixed_order(void) {
  ctx_config_t* config = yices_new_config();
  yices_default_config_for_logic(config, "QF_NIA");
  context_t* ctx = yices_new_context(config);

  term_t x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "x");

  term_t y = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(y, "y");

  assert(!yices_error_code());

  // assertion
  term_t a = yices_arith_gt_atom(x, yices_mul(y, y));
  yices_assert_formula(ctx, a);

  // variable order
  term_t order_vars[2];
  order_vars[0] = y;
  order_vars[1] = x;
  yices_mcsat_set_fixed_var_order(ctx, 2, order_vars);

  // model hint
  model_t* mdl = yices_new_model();
  int32_t code;
  code = yices_model_set_int32(mdl, y, 4);
  if (code < 0) {
    yices_print_error(stderr);
    exit(1);
  }

  term_t vars[2];
  vars[0] = y;
  vars[1] = x;
  
  smt_status_t status;
  status = yices_check_context_with_model_and_hint(ctx, NULL,  mdl, 1, vars, 0);
  assert(!yices_error_code());

  assert(status == STATUS_SAT);

  model_t* res_mdl = yices_get_model(ctx, 1);
  // we should have decided y first and because of the hint its value should be 4
  assert(yices_formula_true_in_model(res_mdl, yices_arith_eq_atom(y, yices_int32(4))));
  // x value should be greater than 16 (because x > y*y and y is assigned 4)
  assert(yices_formula_true_in_model(res_mdl, yices_arith_gt_atom(x, yices_int32(16))));
  
  yices_free_model(mdl);
  yices_free_context(ctx);

}

void check_initial_order(void) {
  ctx_config_t* config = yices_new_config();
  yices_default_config_for_logic(config, "QF_NIA");
  context_t* ctx = yices_new_context(config);

  term_t x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "x");

  term_t y = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(y, "y");

  assert(!yices_error_code());

  // assertion
  term_t a = yices_arith_gt_atom(x, yices_mul(y, y));
  yices_assert_formula(ctx, a);

  // variable order
  term_t order_vars[2];
  order_vars[0] = y;
  order_vars[1] = x;
  yices_mcsat_set_initial_var_order(ctx, 2, order_vars);

  // model hint
  model_t* mdl = yices_new_model();
  int32_t code;
  code = yices_model_set_int32(mdl, y, 4);
  if (code < 0) {
    yices_print_error(stderr);
    exit(1);
  }

  term_t vars[2];
  vars[0] = y;
  vars[1] = x;
  
  smt_status_t status;
  status = yices_check_context_with_model_and_hint(ctx, NULL,  mdl, 1, vars, 0);
  assert(!yices_error_code());

  assert(status == STATUS_SAT);

  model_t* res_mdl = yices_get_model(ctx, 1);
  // we should have decided y first and because of the hint its value should be 4
  assert(yices_formula_true_in_model(res_mdl, yices_arith_eq_atom(y, yices_int32(4))));
  // x value should be greater than 16 (because x > y*y and y is assigned 4)
  assert(yices_formula_true_in_model(res_mdl, yices_arith_gt_atom(x, yices_int32(16))));
  
  yices_free_model(mdl);
  yices_free_context(ctx);

}

int main(void)
{
  if (! yices_has_mcsat()) {
    return 1; // skipped
  }
  yices_init();

  check_fixed_order();
  check_initial_order();

  yices_exit();

  return 0;
}
