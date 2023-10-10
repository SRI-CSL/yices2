/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

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
  param_t *p;

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

  /*
   * Play with solver parameters
   */
  p = yices_new_param_record();
  code = yices_set_param(p, "branching", "positive");
  if (code < 0) {
    printf("Assert failed: ");
    yices_print_error(stdout);
    fflush(stdout);
    goto done;
  }
  
  switch (yices_check_context(ctx, p)) {
  case SMT_STATUS_SAT:
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

  case SMT_STATUS_UNSAT:
    printf("Unsatisfiable\n");
    break;

  case SMT_STATUS_UNKNOWN:
    printf("Status is unknown\n");
    break;

  case SMT_STATUS_IDLE:
  case SMT_STATUS_SEARCHING:
  case SMT_STATUS_INTERRUPTED:
  case SMT_STATUS_ERROR:
    // these codes should not be returned
    printf("Bug: unexpected status returned\n");
    break;
  }

  /*
   * Delete the parameter record: this is optional.
   */
  yices_free_param_record(p);
  
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
