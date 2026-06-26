/*
 * Regression test exercising MCSAT pop + garbage collection across multiple
 * live MCSAT contexts.
 *
 * Background (issue #616):
 *
 *   Yices 2's MCSAT bool plugin has a per-instance CNF manager (cnf_t).
 *   cnf_gc_mark used to cache its progress index across the per-level
 *   marking rounds of one mcsat_gc cycle in a function-local
 *   `static uint32_t i`. That static was shared across every cnf_t
 *   instance in the process, so two concurrent contexts' GC cycles
 *   could in principle clobber each other's marking progress and skip
 *   variables that should have been kept alive.
 *
 *   The fix moves the index into cnf_t::gc_mark_index so that each CNF
 *   instance has its own progress counter.
 *
 * What this test does:
 *
 *   1. Creates two independent MCSAT contexts.
 *   2. Asserts a small Boolean formula in each that forces the bool
 *      plugin to register CNF definitions for a few internal variables,
 *      so cnf_gc_mark has real work to do.
 *   3. Pushes a frame, asserts more lemmas that survive into the bool
 *      plugin's clause database, then triggers a GC by calling
 *      yices_garbage_collect (which fans out to every live context's
 *      mcsat_gc_mark, and hence every cnf_gc_mark).
 *   4. Pops the frame on each context, which itself drives the
 *      mcsat_pop -> mcsat_gc(false) -> bool_plugin_gc_sweep ->
 *      clause_db_gc_sweep path -- the same path that crashed in #616
 *      whenever clause_db_gc_sweep saw a clause whose literal
 *      referenced a variable that good_term considered stale.
 *   5. Re-checks each context to make sure the post-pop bool plugin
 *      state is internally consistent.
 *
 *   The test is deterministic and runs in single-threaded API order,
 *   but the multi-context shape exercises the path where the previous
 *   shared-static was actually shared, and hence is the most direct
 *   single-threaded probe we can write for the regression.
 */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include <yices.h>

static void fail_msg(const char *msg) {
  fprintf(stderr, "test_mcsat_pop_gc_multi_context: %s\n", msg);
  yices_print_error(stderr);
  exit(2);
}

static context_t *make_mcsat_context(void) {
  ctx_config_t *config = yices_new_config();
  if (config == NULL) fail_msg("yices_new_config failed");

  if (yices_set_config(config, "solver-type", "mcsat") < 0) {
    yices_free_config(config);
    fail_msg("yices_set_config solver-type=mcsat failed");
  }

  /* Need push/pop to drive mcsat_pop -> mcsat_gc(false). */
  if (yices_set_config(config, "mode", "push-pop") < 0) {
    yices_free_config(config);
    fail_msg("yices_set_config mode=push-pop failed");
  }

  context_t *ctx = yices_new_context(config);
  yices_free_config(config);
  if (ctx == NULL) fail_msg("yices_new_context failed");
  return ctx;
}

/*
 * Build a small Boolean formula that forces the bool plugin to register
 * CNF definitions for a handful of internal variables. We use OR/AND/IMPLIES
 * over fresh propositional variables so the CNF converter has a non-trivial
 * tree to clausify.
 */
static void assert_base_formula(context_t *ctx, term_t *out_props, int n_props) {
  type_t bool_ty = yices_bool_type();
  for (int i = 0; i < n_props; i++) {
    out_props[i] = yices_new_uninterpreted_term(bool_ty);
    if (out_props[i] == NULL_TERM) fail_msg("yices_new_uninterpreted_term failed");
  }

  /* (or p0 p1 p2 p3) */
  term_t big_or = yices_or(n_props, out_props);
  if (big_or == NULL_TERM) fail_msg("yices_or failed");

  /* (and (=> p0 p1) (=> p1 p2) (=> p2 p3)) */
  term_t implications[3];
  for (int i = 0; i + 1 < n_props && i < 3; i++) {
    implications[i] = yices_implies(out_props[i], out_props[i + 1]);
    if (implications[i] == NULL_TERM) fail_msg("yices_implies failed");
  }
  term_t chain = yices_and(3, implications);
  if (chain == NULL_TERM) fail_msg("yices_and failed");

  if (yices_assert_formula(ctx, big_or) < 0) fail_msg("assert big_or failed");
  if (yices_assert_formula(ctx, chain) < 0) fail_msg("assert chain failed");
}

/*
 * Push a frame and add another fresh-clause workload on top.
 */
static void push_and_extend(context_t *ctx, const term_t *props, int n_props) {
  if (yices_push(ctx) < 0) fail_msg("yices_push failed");

  type_t bool_ty = yices_bool_type();
  term_t q = yices_new_uninterpreted_term(bool_ty);
  if (q == NULL_TERM) fail_msg("yices_new_uninterpreted_term q failed");

  /* (=> q (or p0 p1)) */
  term_t pair[2] = { props[0], props[1 % n_props] };
  term_t local = yices_implies(q, yices_or(2, pair));
  if (local == NULL_TERM) fail_msg("yices_implies for q failed");
  if (yices_assert_formula(ctx, local) < 0) fail_msg("assert local failed");

  /* Drive the solver so the bool plugin actually runs CNF and may learn
   * lemmas/propagations whose clauses live in the bool plugin's
   * clause_db until the next GC. */
  smt_status_t st = yices_check_context(ctx, NULL);
  if (st != YICES_STATUS_SAT && st != YICES_STATUS_UNSAT) {
    fprintf(stderr, "unexpected pre-pop check status: %d\n", (int) st);
    fail_msg("pre-pop check did not return SAT/UNSAT");
  }
}

/*
 * Pop the most recent frame and re-check, exercising the
 * mcsat_pop -> mcsat_gc(false) -> bool_plugin_gc_sweep path.
 */
static void pop_and_recheck(context_t *ctx) {
  if (yices_pop(ctx) < 0) fail_msg("yices_pop failed");

  smt_status_t st = yices_check_context(ctx, NULL);
  if (st != YICES_STATUS_SAT && st != YICES_STATUS_UNSAT) {
    fprintf(stderr, "unexpected post-pop check status: %d\n", (int) st);
    fail_msg("post-pop check did not return SAT/UNSAT");
  }
}

#define N_CTX 3
#define N_PROPS 4

static void test_multi_context_pop_gc(void) {
  context_t *ctx[N_CTX];
  term_t    props[N_CTX][N_PROPS];

  /* (1) Build several live MCSAT contexts in parallel. */
  for (int c = 0; c < N_CTX; c++) {
    ctx[c] = make_mcsat_context();
    assert_base_formula(ctx[c], props[c], N_PROPS);
  }

  /* (2) Push and extend on each, leaving clauses in the bool plugin's
   *     clause database that will need to be garbage-collected on pop.
   *     Doing this for every context first means cnf_gc_mark / mcsat_gc
   *     will see non-trivial state in every CNF instance. */
  for (int c = 0; c < N_CTX; c++) {
    push_and_extend(ctx[c], props[c], N_PROPS);
  }

  /* (3) Trigger a global yices_garbage_collect. With keep_named=1 and
   *     no roots, this fans out to every live context's mcsat_gc_mark,
   *     which is the path that previously shared a single static
   *     marking index across contexts. */
  yices_garbage_collect(NULL, 0, NULL, 0, 1);

  /* (4) Now pop on each context. mcsat_pop runs its own mcsat_gc(false)
   *     internally and asserts clause_db consistency along the way.
   *     If a sibling context's earlier GC left any cnf_gc_mark progress
   *     state that bled into this context (the issue-616 hazard), this
   *     is where it would surface. */
  for (int c = 0; c < N_CTX; c++) {
    pop_and_recheck(ctx[c]);
  }

  /* (5) Push/pop a second time on every context to drive the GC paths
   *     through more iterations and confirm the contexts remain usable. */
  for (int c = 0; c < N_CTX; c++) {
    push_and_extend(ctx[c], props[c], N_PROPS);
  }
  yices_garbage_collect(NULL, 0, NULL, 0, 1);
  for (int c = 0; c < N_CTX; c++) {
    pop_and_recheck(ctx[c]);
  }

  for (int c = 0; c < N_CTX; c++) {
    yices_free_context(ctx[c]);
  }
}

int main(void) {
  if (! yices_has_mcsat()) {
    return 1; /* skipped: build without MCSAT */
  }

  yices_init();
  test_multi_context_pop_gc();
  yices_exit();
  return 0;
}
