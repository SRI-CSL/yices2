/*
 * Test model interpolation with an empty model
 */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "assert.h"

#include <yices.h>

/*
 * Create an MCSAT context 
 */
static context_t *make_mcsat_context(void) {
  ctx_config_t *config;
  context_t *context;
  int32_t code;

  config = yices_new_config();
  code = yices_set_config(config, "solver-type", "mcsat");
  if (code < 0) goto error;
  code = yices_set_config(config, "model-interpolation", "true");
  if (code < 0) goto error;

  context = yices_new_context(config);
  if (context == NULL) goto error;
  yices_free_config(config);
  return context;

 error:
  yices_print_error(stderr);
  yices_free_config(config);
  return NULL;
}

/*
 * Create an unsat assertion:
 * x^2 + y^2 + z^2 + a^2 + b^2 < 1x^2 + y^2 < 1 AND x*y*z*a*b > 1
 * - return variables
 */
static term_t make_unsat_constraint(term_t var[5]) {
  type_t real;
  term_t x, y, z, a, b, p, p1, p2;

  real = yices_real_type();
  x = yices_new_uninterpreted_term(real);
  yices_set_term_name(x, "x");
  y = yices_new_uninterpreted_term(real);
  yices_set_term_name(y, "y");
  z = yices_new_uninterpreted_term(real);
  yices_set_term_name(y, "z");
  a = yices_new_uninterpreted_term(real);
  yices_set_term_name(y, "a");
  b = yices_new_uninterpreted_term(real);
  yices_set_term_name(y, "b");

  var[0] = x;
  var[1] = y;
  var[2] = z;
  var[3] = a;
  var[4] = b;

  term_t arg[5] = {yices_square(x), yices_square(y), yices_square(z), yices_square(a), yices_square(b)};
  p = yices_sum(5, arg); 
  p1 = yices_arith_lt_atom(p, yices_int32(1));    // p < 1

  p2 = yices_arith_gt_atom(yices_product(5, var), yices_int32(1)); // x*y*z*a*b > 1
  return yices_and2(p1, p2);
}


/*
 * Check context with  model and hint
 */
static smt_status_t check_with_model_and_hint(context_t *ctx, model_t *model, term_t assertion, uint32_t n, const term_t t[], uint32_t m) {
  int32_t code = yices_assert_formula(ctx, assertion);
  if (code < 0) {
    yices_print_error(stderr);
    exit(1);
  }

  return yices_check_context_with_model_and_hint(ctx, NULL, model, n, t, m);
}

static void check_unsat_with_empty_model(void) {
  context_t *ctx;
  model_t *model;
  term_t vars[5];
  term_t assertion;

  ctx = make_mcsat_context();
  assertion = make_unsat_constraint(vars);

  model = yices_new_model();

  smt_status_t status;
  status = check_with_model_and_hint(ctx, model, assertion, 0, vars, 0);
  if (status != YICES_STATUS_UNSAT) {
    assert(false);
  }

  term_t interpolant = yices_get_model_interpolant(ctx);
  if (interpolant == NULL_TERM) {
    assert(false);
  }
  
  yices_free_model(model);
  yices_free_context(ctx);
}

int main(void) {  
  if (!yices_has_mcsat()) {
    return 1; // skipped
  }
  
  yices_init();
  
  check_unsat_with_empty_model();

  yices_exit();

  return 0;
}

