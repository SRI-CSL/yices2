/*
 * Reproduce issue233 using the Yices API
 */

/*
 * Here's the spec
 * (set-option :produce-unsat-model-interpolants true)
 * (set-logic QF_BV)
 * (declare-fun x () Bool)
 * (assert (not x))
 * (check-sat)
 * (get-model)
 * (check-sat-assuming-model (x) (true))
 * (check-sat)
 */

#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>

#include <yices.h>

static context_t *make_mcsat_context(void) {
  ctx_config_t *config;
  context_t *context;
  int32_t code;

  config = yices_new_config();
  code = yices_set_config(config, "solver-type", "mcsat");
  if (code < 0) goto error;
  code = yices_set_config(config, "model-interpolation", "true");
  if (code < 0) goto error;
  code = yices_set_config(config, "mode", "push-pop");
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
 * Regular check
 */
static smt_status_t simple_check(context_t *ctx) {
  model_t *full_model;
  smt_status_t result;
  term_t interpolant;

  printf("\nCheck sat:\n");
  fflush(stdout);

  result = yices_check_context(ctx, NULL);

  switch (result) {
  case SMT_STATUS_SAT:
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

  case SMT_STATUS_UNSAT:
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

  case SMT_STATUS_ERROR:
    fprintf(stderr, "Check failed\n");
    yices_print_error(stderr);
    exit(1);

  default:
    fprintf(stderr, "Unexpected status for check\n");
    exit(1);
  }

  printf("---\n");
  fflush(stdout);
  
  return result;
}


/*
 * Check with model and get a model interpolant if the answer is unsat
 */
static smt_status_t check_with_model(context_t *ctx, model_t *model, uint32_t n, const term_t t[]) {
  model_t *full_model;
  term_t interpolant;
  smt_status_t result;

  printf("\nCheck with model:\n");
  if (n == 0) {
    printf("  empty model\n");
  } else {
    printf("  model\n    ");
    yices_print_term_values(stdout, model, n, t);
  }
  printf("\n");
  fflush(stdout);

  result = yices_check_context_with_model(ctx, NULL, model, n, t);
  
  switch (result) {
  case SMT_STATUS_SAT:
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

  case SMT_STATUS_UNSAT:
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
    
  case SMT_STATUS_ERROR:
    fprintf(stderr, "Check with model failed\n");
    yices_print_error(stderr);
    exit(1);

  default:
    fprintf(stderr, "Unexpected status for check with model\n");
    exit(1);
  }

  printf("---\n");
  fflush(stdout);

  return result;
}


static void run_issue233(void) {
  context_t *ctx;
  term_t x;
  int32_t code;
  smt_status_t stat;
  model_t *model;

  ctx = make_mcsat_context();
  if (ctx == NULL) {
    fprintf(stderr, "Context creation failed\n");
    exit(1);
  }

  x = yices_new_uninterpreted_term(yices_bool_type());
  yices_set_term_name(x, "x");

  printf("Assert: (not x))\n");
  fflush(stdout);

  code = yices_assert_formula(ctx, yices_not(x)); // assert not(x)
  if (code < 0) {
    fprintf(stderr, "Assert formula failed\n");
    yices_print_error(stderr);
    exit(1);
  }

  stat = simple_check(ctx);
  if (stat != SMT_STATUS_SAT) {
    fprintf(stderr, "Incorrect answer from check-sat: expected SAT\n");
    exit(1);
  }

  model = yices_new_model();
  code = yices_model_set_bool(model, x, true);
  if (code < 0) {
    fprintf(stderr, "Error in model construction\n");
    yices_print_error(stderr);
    exit(1);
  }

  stat = check_with_model(ctx, model, 1, &x);
  if (stat != SMT_STATUS_UNSAT) {
    fprintf(stderr, "Incorrect answer from check-with-model: expected UNSAT\n");
    exit(1);
  }

  stat = simple_check(ctx);
  if (stat != SMT_STATUS_SAT) {
    fprintf(stderr, "Incorrect answer from check-sat: expected SAT\n");
    exit(1);
  }

  yices_free_model(model);
  yices_free_context(ctx);
}

int main(void) {
  yices_init();
  printf("Testing Yices %s (%s)\n", yices_version, yices_build_date);
  if (yices_has_mcsat()) {
    printf("MCSAT supported\n");
    run_issue233();
  } else {
    printf("MCSAT not supported\n");
  }
  yices_exit();

  return 0;
}
