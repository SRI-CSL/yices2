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

/*
 * API EXAMPLE: SOLVING WITH ASSUMPTIONS AND UNSAT CORES
 */

#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>

#include "yices.h"


/*
 * Print an array of n terms
 */
static void print_terms(uint32_t n, const term_t *a) {
  int32_t code;

  printf("  "); // for proper alignment
  code = yices_pp_term_array(stdout, n, a, 80, 20, 2, false);
  if (code < 0) {
    // error
    fprintf(stderr, "Error in print_term_array: ");
    yices_print_error(stderr);
    exit(1);
  }
}

/*
 * Declare a real variable
 */
static term_t declare_var(const char *name) {
  term_t var;

  var = yices_new_uninterpreted_term(yices_real_type());
  yices_set_term_name(var, name);
  return var;
}

/*
 * Call check and get an unsat core or print a model
 * - n = number of assumptions
 * - a = array of n assumptions
 */
static void check_and_get_core(context_t *ctx, uint32_t n, const term_t *a) {
  int32_t code;
  term_vector_t core;
  model_t *model;

  printf("assumptions:\n");
  print_terms(n, a);

  // NULL here means default search parameters
  switch (yices_check_context_with_assumptions(ctx, NULL, n, a)) {
  case YICES_STATUS_SAT:
    printf("satisfiable\n");
    model = yices_get_model(ctx, true);
    if (model == NULL) {
      fprintf(stderr, "Error in get-model: ");
      yices_print_error(stderr);
      exit(1);
    }
    printf("model:\n  ");
    code = yices_pp_model(stdout, model, 80, 20, 2);
    yices_free_model(model);
    printf("\n");
    break;

  case YICES_STATUS_UNKNOWN:
    printf("the check is inconclusive\n");
    break;

  case YICES_STATUS_UNSAT:
    printf("not satisfiable\n");

    // initialize a vector to store the core
    yices_init_term_vector(&core);

    // get the unsat core
    code = yices_get_unsat_core(ctx, &core);
    if (code < 0) {
      fprintf(stderr, "Error in get_unsat_core: ");
      yices_print_error(stderr);
      exit(1);
    }
    printf("unsat core:\n");
    print_terms(core.size, core.data);
    printf("\n");

    // cleanup
    yices_delete_term_vector(&core);
    break;

  case YICES_STATUS_INTERRUPTED:
    printf("the check was interrupted\n");
    break;

  default:
    fprintf(stderr, "Error in check_with_assumptions: bad status\n");
    exit(1);
  }
}


/*
 * Test: assert (x < y) (x > y) (x = y) in an empty context.
 * Then get an unsat core (should have two elements).
 */
static void unsat_core_test(void) {
  context_t *ctx;
  term_t x, y;
  term_t assumption[3];

  /*
   * Terms x and y
   */
  x = declare_var("x");
  y = declare_var("y");

  /*
   * Three atoms stored in the assumption array
   */
  assumption[0] = yices_arith_lt_atom(x, y); // x < y
  assumption[1] = yices_arith_gt_atom(x, y); // x > y
  assumption[2] = yices_arith_eq_atom(x, y); // x = y

  /*
   * Create an empty context
   */
  ctx = yices_new_context(NULL); // NULL means use the default configuration

  /*
   * Check these three assumption: the unsat core
   * should include two assumptions.
   */
  check_and_get_core(ctx, 3, assumption);

  /*
   * Flip polarities
   */
  assumption[0] = yices_not(assumption[0]);  // x >= y
  assumption[1] = yices_not(assumption[1]);  // x <= y
  assumption[2] = yices_not(assumption[2]);  // x != y

  /*
   * Check again: should get an  unsat core with three elements
   */
  check_and_get_core(ctx, 3, assumption);

  /*
   * Check only the first two assumptions. Should get a model.
   */
  check_and_get_core(ctx, 2, assumption);

  yices_free_context(ctx);
}


int main(void) {
  yices_init();
  unsat_core_test();
  yices_exit();
  return 0;
}
