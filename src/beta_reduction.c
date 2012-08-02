/*
 * BETA REDUCTION OF TERMS
 */

#include <assert.h>
#include <stdint.h>

#include "term_substitution.h"
#include "beta_reduction.h"

#define TRACE 1

#if TRACE

#include "term_printer.h"

static void trace_beta_reduction(term_table_t *tbl, term_t t, term_t u) {
  pp_area_t area;

  area.width = 80;
  area.height = 20;
  area.offset = 8;
  area.stretch = false;
  area.truncate = true;

  printf("--- Beta reduction ---\n");
  printf("input:  ");
  pretty_print_term_exp(stdout, &area, tbl, t);
  printf("output: ");
  pretty_print_term_full(stdout, &area, tbl, u);
  printf("--\n");
}

#endif


/*
 * Check whether t is reducible
 */
bool beta_reducible(term_table_t *table, term_t t) {
  return term_kind(table, t) == APP_TERM && 
    term_kind(table, app_term_desc(table, t)->arg[0]) == LAMBDA_TERM;
}


/*
 * Apply a (lambda (x_0 ... x_n-1) t) to arguments arg[0 ... n-1]
 * - lambda is the term_descriptor of (lambda (x_0 ... x_n) t)
 * - arg = array of n terms
 */
static term_t apply_beta_rule(term_manager_t *mngr, composite_term_t *lambda, term_t *arg) {
  term_subst_t subst;
  uint32_t n;
  term_t u;

  assert(lambda->arity >= 2);
  n = lambda->arity - 1; // number of variables
  init_term_subst(&subst, mngr, n, lambda->arg, arg);
  u = apply_term_subst(&subst, lambda->arg[n]);
  delete_term_subst(&subst);

  return u;
}


/*
 * Apply beta-reduction to t
 */
term_t beta_reduce(term_manager_t *mngr, term_t t) {
  term_table_t *tbl;
  composite_term_t *app;
  term_t f, u;

  u = t;
  tbl = term_manager_get_terms(mngr);
  if (term_kind(tbl, t) == APP_TERM) {
    app = app_term_desc(tbl, t);
    f = app->arg[0];
    if (term_kind(tbl, f) == LAMBDA_TERM) {
      u = apply_beta_rule(mngr, lambda_term_desc(tbl, f), app->arg + 1);

#if TRACE
      trace_beta_reduction(tbl, t, u);
#endif

    }
  }

  return u;
}
