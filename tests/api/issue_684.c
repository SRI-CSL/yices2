/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * Issue #684: MCSAT model interpolants over a scalar type.
 *
 * The NA plugin owns scalar types and propagates the value of each scalar
 * constant at the base level with no reasons. The explanation of such a
 * propagation was an arithmetic constant, so the interpolant for
 *   y = c2, x = y   with model x = c1
 * was (= x 2), which is ill-sorted, instead of (= x c2).
 */

#include <stdio.h>
#include <stdlib.h>

#include <yices.h>

static void fail(const char *msg) {
  yices_print_error(stderr);
  fprintf(stderr, "%s\n", msg);
  exit(2);
}

static void run(int with_push) {
  ctx_config_t *cfg;
  context_t *ctx;
  model_t *mdl;
  type_t s;
  term_t c1, c2, x, y, itp;
  smt_status_t st;

  cfg = yices_new_config();
  if (yices_set_config(cfg, "solver-type", "mcsat") < 0 ||
      yices_set_config(cfg, "model-interpolation", "true") < 0) {
    fail("bad configuration");
  }
  ctx = yices_new_context(cfg);
  yices_free_config(cfg);
  if (ctx == NULL) fail("failed to create context");

  s = yices_new_scalar_type(3);
  c1 = yices_constant(s, 1);
  c2 = yices_constant(s, 2);
  x = yices_new_uninterpreted_term(s);
  y = yices_new_uninterpreted_term(s);
  yices_set_term_name(c1, "c1");
  yices_set_term_name(c2, "c2");
  yices_set_term_name(x, "x");
  yices_set_term_name(y, "y");

  if (with_push) yices_push(ctx);
  if (yices_assert_formula(ctx, yices_eq(y, c2)) < 0 ||
      yices_assert_formula(ctx, yices_eq(x, y)) < 0) {
    fail("assert failed");
  }

  mdl = yices_new_model();
  yices_model_set_term(mdl, x, c1);
  st = yices_check_context_with_model(ctx, NULL, mdl, 1, &x);
  if (st != YICES_STATUS_UNSAT) {
    fprintf(stderr, "expected unsat, got status %d\n", (int) st);
    exit(1);
  }

  itp = yices_get_model_interpolant(ctx);
  if (itp == NULL_TERM) fail("no interpolant");
  if (itp != yices_eq(x, c2)) {
    fprintf(stderr, "wrong interpolant: ");
    yices_pp_term(stderr, itp, 120, 4, 0);
    exit(1);
  }

  yices_free_model(mdl);
  yices_free_context(ctx);
}

int main(void) {
  if (!yices_has_mcsat()) {
    return 1; /* skipped */
  }
  yices_init();
  run(0);
  run(1);
  yices_exit();
  printf("ok\n");
  return 0;
}
