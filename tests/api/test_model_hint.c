/*
 * Test mcsat model hint api
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
 * Create assertion x^2 + y^2 < 1
 * - return terms x and y in var:
 *   var[0] = x
 *   var[1] = y
 */
static term_t make_circle_constraint(term_t var[2]) {
  type_t real;
  term_t x, y, p;

  real = yices_real_type();
  x = yices_new_uninterpreted_term(real);
  yices_set_term_name(x, "x");
  y = yices_new_uninterpreted_term(real);
  yices_set_term_name(y, "y");

  var[0] = x;
  var[1] = y;

  p = yices_add(yices_square(x), yices_square(y)); // p is x^2 + y^2
  return yices_arith_lt_atom(p, yices_int32(1));    // p < 1
}

/*
 * Create an unsat assertion: x^2 + y^2 < 1 AND x>2
 * - return variables x and y in var[0] and var[1], respectively.
 */
static term_t make_unsat_constraint(term_t var[2]) {
  term_t p1, p2;

  p1 = make_circle_constraint(var); // x^2 + y^2 < 1
  p2 = yices_arith_gt_atom(var[0], yices_int32(2)); // x>2
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


static void check_with_sat_model(bool use_hint) {
  context_t *ctx;
  model_t *model;
  term_t vars[2];
  term_t assertion;
  int32_t code;

  ctx = make_mcsat_context();
  assertion = make_circle_constraint(vars);  // x^2 + y^2 < 1

  model = yices_new_model();
  code = yices_model_set_int32(model, vars[0], 0); // x == 0
  if (code < 0) {
    yices_print_error(stderr);
    exit(1);
  }

  smt_status_t status;
  if (use_hint) {
    status = check_with_model_and_hint(ctx, model, assertion, 1, vars, 0);
    assert(status == STATUS_SAT);
  } else {
    status = check_with_model_and_hint(ctx, model, assertion, 1, vars, 1);
    assert(status == STATUS_SAT);
  }
  yices_free_model(model);
  yices_free_context(ctx);
}


static void check_with_unsat_model(bool use_hint) {
  context_t *ctx;
  model_t *model;
  term_t vars[2];
  term_t assertion;
  int32_t code;

  ctx = make_mcsat_context();
  assertion = make_circle_constraint(vars);  // x^2 + y^2 < 1

  model = yices_new_model();
  code = yices_model_set_int32(model, vars[0], 1); // x == 1
  if (code < 0) {
    yices_print_error(stderr);
    exit(1);
  }

  smt_status_t status;
  if (use_hint) {
    status = check_with_model_and_hint(ctx, model, assertion, 1, vars, 0);
    assert(status == STATUS_SAT);
  } else {
    status = check_with_model_and_hint(ctx, model, assertion, 1, vars, 1);
    assert(status == STATUS_UNSAT);
  }
  yices_free_model(model);
  yices_free_context(ctx);
}

static void check_sat_with_empty_model(void) {
  context_t *ctx;
  model_t *model;
  term_t vars[2];
  term_t assertion;

  ctx = make_mcsat_context();
  assertion = make_circle_constraint(vars);  // x^2 + y^2 < 1

  model = yices_new_model();

  smt_status_t status;
  status = check_with_model_and_hint(ctx, model, assertion, 0, vars, 0);
  assert(status == STATUS_SAT);
  yices_free_model(model);
  yices_free_context(ctx);
}

static void check_unsat_with_empty_model(void) {
  context_t *ctx;
  model_t *model;
  term_t vars[2];
  term_t assertion;

  ctx = make_mcsat_context();
  assertion = make_unsat_constraint(vars);

  model = yices_new_model();

  smt_status_t status;
  status = check_with_model_and_hint(ctx, model, assertion, 0, vars, 0);
  assert(status == STATUS_UNSAT);

  yices_free_model(model);
  yices_free_context(ctx);
}

static void check_unsat_with_model(bool use_hint) {
  context_t *ctx;
  model_t *model;
  term_t vars[2];
  term_t assertion;
  int32_t code;

  ctx = make_mcsat_context();
  assertion = make_unsat_constraint(vars);

  model = yices_new_model();
  code = yices_model_set_int32(model, vars[0], 0); // x == 0
  if (code < 0) {
    yices_print_error(stderr);
    exit(1);
  }

  smt_status_t status;
  if (use_hint) {
    status = check_with_model_and_hint(ctx, model, assertion, 1, vars, 0);
    assert(status == STATUS_UNSAT);
  } else {
    status = check_with_model_and_hint(ctx, model, assertion, 1, vars, 1);
    assert(status == STATUS_UNSAT);
  }

  yices_free_model(model);
  yices_free_context(ctx);
}


int main(void) {  
  yices_init();
  if (yices_has_mcsat()) {
    printf("MCSAT supported\n");
    check_with_sat_model(false);
    check_with_sat_model(true);
    check_with_unsat_model(false);
    check_with_unsat_model(true);
    check_sat_with_empty_model();
    check_unsat_with_empty_model();
    check_unsat_with_model(false);
    check_unsat_with_model(true);
  } else {
    printf("MCSAT not supported\n");   
  }
  yices_exit();

  return 0;
}

