/*
 * Test unsat core construction with assumptions in an MCSAT context.
 */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include <yices.h>

static void fail(const char *msg) {
  fprintf(stderr, "%s\n", msg);
  exit(2);
}

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

static bool has_term(const term_vector_t *v, term_t t) {
  uint32_t i;

  for (i = 0; i < v->size; i++) {
    if (v->data[i] == t) {
      return true;
    }
  }
  return false;
}

static void test_unsat_core_with_assumptions_mcsat(void) {
  context_t *ctx;
  type_t bool_ty;
  term_t p, q, c;
  term_t assumptions[2];
  term_vector_t core;
  smt_status_t status;
  int32_t code;

  ctx = make_mcsat_context();
  if (ctx == NULL) {
    fail("failed to create mcsat context");
  }

  bool_ty = yices_bool_type();
  p = yices_new_uninterpreted_term(bool_ty);
  q = yices_new_uninterpreted_term(bool_ty);

  /*
   * Base constraint: not (p and q), encoded as (or (not p) (not q)).
   * With assumptions p and q, the context is UNSAT and both assumptions
   * are required.
   */
  c = yices_or2(yices_not(p), yices_not(q));
  code = yices_assert_formula(ctx, c);
  if (code < 0) {
    yices_print_error(stderr);
    fail("yices_assert_formula failed");
  }

  assumptions[0] = p;
  assumptions[1] = q;

  status = yices_check_context_with_assumptions(ctx, NULL, 2, assumptions);
  if (status != YICES_STATUS_UNSAT) {
    yices_print_error(stderr);
    fail("expected UNSAT from yices_check_context_with_assumptions");
  }

  yices_init_term_vector(&core);
  code = yices_get_unsat_core(ctx, &core);
  if (code < 0) {
    yices_print_error(stderr);
    fail("yices_get_unsat_core failed");
  }
  if (core.size != 2 || !has_term(&core, p) || !has_term(&core, q)) {
    fail("unexpected unsat core content");
  }
  yices_delete_term_vector(&core);

  yices_free_context(ctx);
}

int main(void) {
  if (! yices_has_mcsat()) {
    return 1; // skipped
  }

  yices_init();
  test_unsat_core_with_assumptions_mcsat();
  yices_exit();

  return 0;
}
