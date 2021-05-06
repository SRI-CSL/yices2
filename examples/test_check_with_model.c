/*
 * Examples of check_with_model and model interpolants
 */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include <yices.h>

/*
 * Create an MCSAT context that supports model interpolants
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
 * Check with model and get a model interpolant if the answer is unsat
 */
static void check_with_model(context_t *ctx, model_t *model, term_t assertion, uint32_t n, const term_t t[]) {
  model_t *full_model;
  term_t interpolant;
  int32_t code;

  printf("\nCheck with model:\n");
  printf("  assertion:\n    ");
  yices_pp_term(stdout, assertion, 100, 100, 4);
  if (n == 0) {
    printf("  empty model\n");
  } else {
    printf("  model\n    ");
    yices_print_term_values(stdout, model, n, t);
  }
  printf("\n");
  fflush(stdout);

  code = yices_assert_formula(ctx, assertion);
  if (code < 0) {
    fprintf(stderr, "Assert formula failed\n");
    yices_print_error(stderr);
    exit(1);
  }

  switch (yices_check_context_with_model(ctx, NULL, model, n, t)) {
  case STATUS_SAT:
    printf("SATISFIABLE\n");
    full_model = yices_get_model(ctx, true);
    if (full_model != NULL) {
      printf("  full model:\n    ");
      yices_pp_model(stdout, full_model, 100, 100, 4);
      yices_free_model(full_model);
    } else {
      fprintf(stderr, "Failed to get a full model\n");
      yices_print_error(stderr);
      exit(1);
    }
    break;

  case STATUS_UNSAT:
    printf("UNSATISFIABLE\n");
    interpolant = yices_get_model_interpolant(ctx);
    if (interpolant != NULL_TERM) {
      printf("  model interpolant:\n    ");
      yices_pp_term(stdout, interpolant, 100, 100, 4);     
    } else {
      fprintf(stderr, "Failed to get a model interpolant\n");
      yices_print_error(stderr);
      exit(1);
    }
    break;
    
  case STATUS_ERROR:
    fprintf(stderr, "Check with model failed\n");
    yices_print_error(stderr);
    exit(1);

  default:
    fprintf(stderr, "Unexpected status for check with model\n");
    exit(1);
  }

  printf("---\n");
  fflush(stdout);
}


/*
 * Regular check. get a model interpolant if the answer is unsat
 */
static void check(context_t *ctx, term_t assertion) {
  model_t *full_model;
  term_t interpolant;
  int32_t code;

  printf("\nCheck without model:\n");
  printf("  assertion:\n    ");
  yices_pp_term(stdout, assertion, 100, 100, 4);
  printf("\n");
  fflush(stdout);

  code = yices_assert_formula(ctx, assertion);
  if (code < 0) {
    fprintf(stderr, "Assert formula failed\n");
    yices_print_error(stderr);
    exit(1);
  }

  switch (yices_check_context(ctx, NULL)) {
  case STATUS_SAT:
    printf("SATISFIABLE\n");
    full_model = yices_get_model(ctx, true);
    if (full_model != NULL) {
      printf("  full model:\n    ");
      yices_pp_model(stdout, full_model, 100, 100, 4);
      yices_free_model(full_model);
    } else {
      fprintf(stderr, "Failed to get a full model\n");
      yices_print_error(stderr);
      exit(1);
    }
    break;

  case STATUS_UNSAT:
    printf("UNSATISFIABLE\n");
    interpolant = yices_get_model_interpolant(ctx);
    if (interpolant != NULL_TERM) {
      printf("  model interpolant:\n    ");
      yices_pp_term(stdout, interpolant, 100, 100, 4);     
    } else {
      fprintf(stderr, "Failed to get a model interpolant\n");
      yices_print_error(stderr);
      exit(1);
    }
    break;
    
  case STATUS_ERROR:
    fprintf(stderr, "Check failed\n");
    yices_print_error(stderr);
    exit(1);

  default:
    fprintf(stderr, "Unexpected status for check\n");
    exit(1);
  }

  printf("---\n");
  fflush(stdout);
}


static void check_with_sat_model(void) {
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
    fprintf(stderr, "Error in model construction\n");
    yices_print_error(stderr);
    exit(1);
  }

  check_with_model(ctx, model, assertion, 1, vars);
  yices_free_model(model);
  yices_free_context(ctx);
}


static void check_with_unsat_model(void) {
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
    fprintf(stderr, "Error in model construction\n");
    yices_print_error(stderr);
    exit(1);
  }

  check_with_model(ctx, model, assertion, 1, vars);
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
  check_with_model(ctx, model, assertion, 0, vars);
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
  check_with_model(ctx, model, assertion, 0, vars);
  yices_free_model(model);
  yices_free_context(ctx);
}

static void check_unsat_with_model(void) {
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
    fprintf(stderr, "Error in model construction\n");
    yices_print_error(stderr);
    exit(1);
  }

  check_with_model(ctx, model, assertion, 1, vars);
  yices_free_model(model);
  yices_free_context(ctx);
}

static void check_regular_unsat(void) {
  context_t *ctx;
  term_t assertion;
  term_t vars[2];
  
  ctx = make_mcsat_context();
  assertion = make_unsat_constraint(vars);
  check(ctx, assertion);
  yices_free_context(ctx);
}

static void check_regular_sat(void) {
  context_t *ctx;
  term_t assertion;
  term_t vars[2];
  
  ctx = make_mcsat_context();
  assertion = make_circle_constraint(vars);
  check(ctx, assertion);
  yices_free_context(ctx);
}

int main(void) {  
  yices_init();
  printf("Testing Yices %s (%s)\n", yices_version, yices_build_date);
  if (yices_has_mcsat()) {
    printf("MCSAT supported\n");
    check_with_sat_model();
    check_with_unsat_model();
    check_sat_with_empty_model();
    check_unsat_with_empty_model();
    check_unsat_with_model();
    check_regular_unsat();
    check_regular_sat();
  } else {
    printf("MCSAT not supported\n");   
  }
  yices_exit();

  return 0;
}

