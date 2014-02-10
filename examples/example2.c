#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

#include <yices.h>

int main(void) {
  type_t real;
  term_t t, a;
  int32_t code;
  context_t *ctx;
  model_t *mdl;

  /*
   * Global initialization: this must called first.
   */
  yices_init();

  /*
   * Create an uninterpreted term of type real and call it "x"
   */
  real = yices_real_type();
  t = yices_new_uninterpreted_term(real);
  code = yices_set_term_name(t, "x");

  /*
   * If code is negative, something went wrong
   */
  if (code < 0) {
    printf("Error in yices_set_term\n");
    yices_print_error(stdout);
    fflush(stdout);
    goto done;
  }


  /*
   * Create the atom (x > 0)
   */
  a = yices_arith_gt0_atom(t);

  /*
   * Print the atom:
   */
  printf("Atom: ");
  yices_pp_term(stdout, a, 120, 2, 6);

  /*
   * Check that (x > 0) is satisfiable and get a model
   * - create a context
   * - assert atom 'a' in this context
   * - check that the context is satisfiable
   */
  ctx = yices_new_context(NULL);  // NULL means use the default configuration
  code = yices_assert_formula(ctx, a);
  if (code < 0) {
    printf("Assert failed: ");
    yices_print_error(stdout);
    fflush(stdout);
    goto done;
  }

  switch (yices_check_context(ctx, NULL)) { // NULL means default heuristics
  case STATUS_SAT:
    // build the model and print it
    printf("Satisfiable\n");
    mdl = yices_get_model(ctx, true);
    code = yices_pp_model(stdout, mdl, 120, 100, 0);
    if (code < 0) {
      printf("Print model failed: ");
      yices_print_error(stdout);
      fflush(stdout);
      goto done;
    }
    // cleanup: delete the model
    yices_free_model(mdl);
    break;

  case STATUS_UNSAT:
    printf("Unsatisfiable\n");
    break;

  case STATUS_UNKNOWN:
    printf("Status is unknown\n");
    break;

  case STATUS_IDLE:
  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
  case STATUS_ERROR:
    // these codes should not be returned
    printf("Bug: unexpected status returned\n");
    break;
  }

  /*
   * Delete the context: this is optional since yices_exit
   * would do it anyway.
   */
  yices_free_context(ctx);

 done:
  /*
   * Global cleanup: free all memory used by Yices
   */
  yices_exit();

  return 0;
}
