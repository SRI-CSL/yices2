/*
 * Reproduce test02m using the Yices API
 */

/*
 * Here's the spec
 *
 * (set-option :produce-unsat-model-interpolants true)
 * (set-logic QF_LRA)
 * (declare-const x Real)
 * (declare-const y Real)
 * (declare-const z Real)
 * (assert (> (+ x y z) 0))
 *
 * (push 1)
 * (check-sat-assuming-model (x y z) ((- 1) (- 2) 3))
 * (get-unsat-model-interpolant) ;; result was unsat, should print
 * (get-unsat-model-interpolant) ;; no change, should still print
 * (pop 1)
 *
 * (get-unsat-model-interpolant) ;; no-checksat, error
 *
 * (check-sat-assuming-model (x y z) ((- 1) (- 2) 3))
 * (get-unsat-model-interpolant) ;; unsat, should print
 *
 * (check-sat)  ;; sat
 * (get-unsat-model-interpolant) ;; error
 *
 * (check-sat-assuming-model (x y z) ((- 1) (- 2) 3))
 * (get-unsat-model-interpolant) ;; unsat, should print
 *
 * (push 1)
 * (get-unsat-model-interpolant) ;; idle, error
 * (pop 1)
 *
 * (check-sat-assuming-model (x y z) ((- 1) (- 2) 3))
 * (get-unsat-model-interpolant) ;; unsat, should print
 *
 * (assert true)
 * (get-unsat-model-interpolant) ;; error (missing check)
 *
 * (assert false)
 * (get-unsat-model-interpolant) ;; error (missing check)
 *
 * (check-sat)
 * (get-unsat-model-interpolant) ;; trivial unsat, should print false
 * (check-sat-assuming-model (x y z) ((- 1) (- 2) 3))
 * (get-unsat-model-interpolant) ;; unsat, should still print false
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

  printf("Check sat:\n");
  fflush(stdout);

  result = yices_check_context(ctx, NULL);

  switch (result) {
  case YICES_STATUS_SAT:
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

  case YICES_STATUS_UNSAT:
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

  case YICES_STATUS_ERROR:
    fprintf(stderr, "Check failed\n");
    yices_print_error(stderr);
    break;

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

  printf("Check with model:\n");
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
  case YICES_STATUS_SAT:
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

  case YICES_STATUS_UNSAT:
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
    
  case YICES_STATUS_ERROR:
    fprintf(stderr, "Check with model failed\n");
    yices_print_error(stderr);
    break;

  default:
    fprintf(stderr, "Unexpected status for check with model\n");
    exit(1);
  }

  printf("---\n");
  fflush(stdout);

  return result;
}


static void do_assert(context_t *ctx, term_t assertion) {
  int32_t code;

  printf("assert\n");
  code = yices_assert_formula(ctx, assertion);
  if (code < 0) {
    fprintf(stderr, "Assert formula failed\n");
    yices_print_error(stderr);
    exit(1);
  }
  printf("---\n");
  fflush(stdout);
}

static void do_push(context_t *ctx) {
  int32_t code;

  printf("push\n");
  code = yices_push(ctx);
  if (code < 0) {
    fprintf(stderr, "Push failed\n");
    yices_print_error(stderr);
    exit(1);
  }  
  printf("---\n");
  fflush(stdout);
}

static void do_pop(context_t *ctx) {
  int32_t code;

  printf("pop\n");
  code = yices_pop(ctx);
  if (code < 0) {
    fprintf(stderr, "Pop failed\n");
    yices_print_error(stderr);
    exit(1);
  }  
  printf("---\n");
  fflush(stdout);
}

static void get_interpolant(context_t *ctx) {
  term_t interpolant;

  printf("get interpolant\n");
  interpolant = yices_get_model_interpolant(ctx);
  if (interpolant != NULL_TERM) {
    printf("  model interpolant:\n    ");
    yices_pp_term(stdout, interpolant, 100, 100, 4);     
  } else {
    fprintf(stderr, "Incorrect answer from get-interpolant\n");
    yices_print_error(stderr);
    exit(1);
  }
  printf("---\n");
  fflush(stdout);
}

static void no_interpolant(context_t *ctx) {
  term_t interpolant;

  printf("get interpolant\n");
  interpolant = yices_get_model_interpolant(ctx);
  if (interpolant != NULL_TERM) {
    printf("  model interpolant:\n    ");
    yices_pp_term(stdout, interpolant, 100, 100, 4);     
    fprintf(stderr, "Incorrect answer from get-interpolant: expected NULL_TERM\n");
    exit(1);
  } else {
    fprintf(stderr, "Correct answer from get-interpolant: NULL_TERM\n");
    yices_print_error(stderr);
  }
  printf("---\n");
  fflush(stdout);
}


static void run_test02m(void) {
  context_t *ctx;
  term_t var[3];
  term_t assertion;
  int32_t code;
  smt_status_t stat;
  model_t *model;

  ctx = make_mcsat_context();
  if (ctx == NULL) {
    fprintf(stderr, "Context creation failed\n");
    exit(1);
  }

  // three real variables x, y, z
  var[0] = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(var[0], "x");
  var[1] = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(var[1], "y");
  var[2] = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(var[2], "z");

  // assertion: x + y + z > 0
  assertion = yices_arith_gt0_atom(yices_sum(3, var));
  printf("Assertion:\n    ");
  yices_pp_term(stdout, assertion, 100, 100, 4);
  fflush(stdout);

  // model: x = -1, y = -2, z = 3
  model = yices_new_model();
  code = yices_model_set_int32(model, var[0], -1);  // x = -1
  if (code >= 0) code = yices_model_set_int32(model, var[1], -2); // y = -2
  if (code >= 0) code = yices_model_set_int32(model, var[2], 3);  // z = 3
  if (code < 0) {
    fprintf(stderr, "Error in model construction\n");
    yices_print_error(stderr);
    exit(1);
  }

  // assert x + y + z > 0
  do_assert(ctx, assertion);

  // push
  do_push(ctx);

  // check-with-model
  stat = check_with_model(ctx, model, 3, var);
  if (stat != YICES_STATUS_UNSAT) {
    fprintf(stderr, "Incorrect answer from check-with-model: expected UNSAT\n");
    exit(1);
  }

  // get-interpolant (second call)
  get_interpolant(ctx);

  // pop
  do_pop(ctx);

  // get-interpolant should fail
  no_interpolant(ctx);

  // check with model: unsat + interpolant
  stat = check_with_model(ctx, model, 3, var);
  if (stat != YICES_STATUS_UNSAT) {
    fprintf(stderr, "Incorrect answer from check-with-model: expected UNSAT\n");
    exit(1);
  }

  // check-sat: sat
  stat = simple_check(ctx);
  if (stat != YICES_STATUS_SAT) {
    fprintf(stderr, "Incorrect answer from check-sat: expected SAT\n");
    exit(1);
  }

  // get-interpolant should fail
  no_interpolant(ctx);

  // check with model: unsat + interpolant
  stat = check_with_model(ctx, model, 3, var);
  if (stat != YICES_STATUS_UNSAT) {
    fprintf(stderr, "Incorrect answer from check-with-model: expected UNSAT\n");
    exit(1);
  }

  // push
  do_push(ctx);
  
  // get interpolant should fail
  no_interpolant(ctx);

  // pop
  do_pop(ctx);

  // check with model: unsat + interpolant
  stat = check_with_model(ctx, model, 3, var);
  if (stat != YICES_STATUS_UNSAT) {
    fprintf(stderr, "Incorrect answer from check-with-model: expected UNSAT\n");
    exit(1);
  }

  // assert true
  do_assert(ctx, yices_true());

  // get interpolant should fail
  no_interpolant(ctx);

  // assert false
  do_assert(ctx, yices_false());

  // get interpolant should still fail
  no_interpolant(ctx);

  // simple check: expect UNSAT + interpolant
  stat = simple_check(ctx);
  if (stat != YICES_STATUS_UNSAT) {
    fprintf(stderr, "Incorrect answer from check: expected UNSAT\n");
    exit(1);
  }

  // check with model: unsat + interpolant (should be false)
  stat = check_with_model(ctx, model, 3, var);
  if (stat != YICES_STATUS_UNSAT) {
    fprintf(stderr, "Incorrect answer from check-with-model: expected UNSAT\n");
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
    run_test02m();
  } else {
    printf("MCSAT not supported\n");
  }
  yices_exit();

  return 0;
}
