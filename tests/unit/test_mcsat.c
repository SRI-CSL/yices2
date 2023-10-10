/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
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
 * TEST MCSAT
 */

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>

#if HAVE_MCSAT
#include <poly/algebraic_number.h>
#endif

#include "yices.h"

/*
 * Print an error message then exit
 */
static void print_error(void) {
  char *s;

  s = yices_error_string();
  fprintf(stderr, "Yices error: %s\n", s);
  yices_free_string(s);
  exit(1);
}

/*
 * Convert to string
 */
static char *term_to_string(term_t term) {
  char *s; 

  s = yices_term_to_string(term, 80, 20, 0);
  if (s == NULL) print_error();
  return s;
}

/*
 * Create a real variable.
 */
static term_t declare_var(const char *name) {
  term_t x;

  x = yices_new_uninterpreted_term(yices_real_type());
  if (x < 0) print_error();
  yices_set_term_name(x, name);
  return x;
}


/*
 * Create a context for QF_NRA
 */
static context_t *make_context(void) {
  ctx_config_t *cfg;
  context_t *ctx;
  int32_t code;

  cfg = yices_new_config();
  code = yices_default_config_for_logic(cfg, "QF_NRA");
  if (code < 0) print_error();
  code = yices_set_config(cfg, "mode", "one-shot");
  if (code < 0) print_error();
  
  ctx = yices_new_context(cfg);
  if (ctx == NULL) print_error();
  yices_free_config(cfg);

  return ctx;
}


/*
 * Value of term t in mdl as an algebraic number
 */
static void show_algebraic_value(model_t *mdl, term_t t) {
#if HAVE_MCSAT
  lp_algebraic_number_t n;
  int32_t code;

  code = yices_get_algebraic_number_value(mdl, t, &n);
  if (code < 0) print_error();
  lp_algebraic_number_print(&n, stdout);
  fflush(stdout);
  lp_algebraic_number_destruct(&n);
#endif
}


static void test_mcsat(void) {
  context_t *ctx;
  model_t *mdl;
  term_t x, p;
  char *s;
  int32_t code;
  smt_status_t status;
  double root;

  x = declare_var("x");
  p = yices_parse_term("(= (* x x) 2)");
  if (p < 0) print_error();

  s = term_to_string(p);
  printf("Assertion: %s\n", s);
  fflush(stdout);
  yices_free_string(s);
  
  ctx = make_context();
  code = yices_assert_formula(ctx, p);
  if (code < 0) print_error();

  status = yices_check_context(ctx, NULL);
  if (status != SMT_STATUS_SAT) {
    fprintf(stderr, "Test failed: status != SMT_STATUS_SAT\n");
    exit(1);
  }

  printf("Satisfiable\n");
  mdl = yices_get_model(ctx, true);
  if (mdl == NULL) print_error();
  printf("Model:\n");
  yices_pp_model(stdout, mdl, 80, 20, 0);
  printf("\n");

  // test: get value as a double
  code = yices_get_double_value(mdl, x, &root);
  if (code < 0) print_error();
  printf("double value of x = %f\n", root);

  // test use the lp_algebraic_number interface
  printf("algebraic value of x = ");
  show_algebraic_value(mdl, x);
  printf("\n");

  printf("Test succeeded\n");

  // cleanup
  yices_free_model(mdl);
  yices_free_context(ctx);
}

int main(void) {
  if (yices_has_mcsat()) {
    yices_init();
    test_mcsat();
    yices_exit();
  } else {
    fprintf(stderr, "MCSAT is not supported by this Yices build\n");
  }

  return 0;
}
