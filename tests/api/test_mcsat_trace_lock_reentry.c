/*
 * Regression test for MCSAT trace checks under THREAD_SAFE builds.
 *
 * Before the lock-free trace-check fix, these traces could re-enter lock-taking
 * API calls while the global lock was already held by yices_check_context.
 * That caused deadlock.
 */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#if defined(_WIN32)
#include <windows.h>
#else
#include <signal.h>
#include <unistd.h>
#endif

#include <yices.h>

static void fail(const char *msg) {
  fprintf(stderr, "%s\n", msg);
  yices_print_error(stderr);
  exit(2);
}

#if defined(_WIN32)
static HANDLE watchdog_stop_event = NULL;
static HANDLE watchdog_thread = NULL;

static DWORD WINAPI watchdog_main(LPVOID arg) {
  HANDLE stop_event = (HANDLE) arg;
  DWORD status = WaitForSingleObject(stop_event, 15000);
  if (status == WAIT_TIMEOUT) {
    fprintf(stderr, "timeout: possible deadlock\n");
    fflush(stderr);
    ExitProcess(3);
  }
  return 0;
}

static void start_deadlock_watchdog(void) {
  watchdog_stop_event = CreateEvent(NULL, TRUE, FALSE, NULL);
  if (watchdog_stop_event == NULL) {
    fprintf(stderr, "failed to create watchdog stop event\n");
    exit(2);
  }

  watchdog_thread = CreateThread(NULL, 0, watchdog_main, watchdog_stop_event, 0, NULL);
  if (watchdog_thread == NULL) {
    CloseHandle(watchdog_stop_event);
    watchdog_stop_event = NULL;
    fprintf(stderr, "failed to create watchdog thread\n");
    exit(2);
  }
}

static void stop_deadlock_watchdog(void) {
  if (watchdog_stop_event != NULL) {
    SetEvent(watchdog_stop_event);
  }
  if (watchdog_thread != NULL) {
    WaitForSingleObject(watchdog_thread, INFINITE);
    CloseHandle(watchdog_thread);
    watchdog_thread = NULL;
  }
  if (watchdog_stop_event != NULL) {
    CloseHandle(watchdog_stop_event);
    watchdog_stop_event = NULL;
  }
}
#else
static void on_alarm(int sig) {
  (void) sig;
  fprintf(stderr, "timeout: possible deadlock\n");
  exit(3);
}

static void start_deadlock_watchdog(void) {
  signal(SIGALRM, on_alarm);
  alarm(15);
}

static void stop_deadlock_watchdog(void) {
  alarm(0);
}
#endif

static context_t *make_mcsat_context_with_trace(const char *logic, const char *trace_tags) {
  ctx_config_t *config;
  context_t *context;
  int32_t code;

  config = yices_new_config();
  if (logic != NULL) {
    code = yices_default_config_for_logic(config, logic);
    if (code < 0) {
      yices_free_config(config);
      return NULL;
    }
  }
  code = yices_set_config(config, "solver-type", "mcsat");
  if (code < 0) {
    yices_free_config(config);
    return NULL;
  }
  code = yices_set_config(config, "trace", trace_tags);
  if (code < 0) {
    yices_free_config(config);
    return NULL;
  }

  context = yices_new_context(config);
  yices_free_config(config);
  return context;
}

/*
 * Trigger paths:
 * yices_check_context -> mcsat solve -> (trace) conflict_check(...)
 * yices_check_context -> mcsat solve -> BV plugin conflict explanation
 * -> (trace) bv_explainer_check_conflict(...)
 *
 * Formula adapted from tests/regress/mcsat/bv/issue145.smt2.
 */
static void test_mcsat_bv_conflict_trace_issue145(void) {
  context_t *ctx;
  type_t bv5, bv4;
  term_t x, y;
  term_t e3, e4, e5, e8, e11, e14, e18;
  smt_status_t status;
  int32_t code;

  ctx = make_mcsat_context_with_trace("QF_BV", "mcsat::conflict::check,mcsat::bv::conflict::check");
  if (ctx == NULL) {
    fail("failed to create mcsat context (bv conflict trace)");
  }

  bv5 = yices_bv_type(5);
  bv4 = yices_bv_type(4);
  x = yices_new_uninterpreted_term(bv5);
  y = yices_new_uninterpreted_term(bv4);

  e3 = yices_bvsrem(yices_sign_extend(y, 1), x);
  e4 = yices_bvsub(e3, yices_bvconst_uint32(5, 0));
  e5 = yices_bvgt_atom(e3, yices_zero_extend(y, 1));
  e8 = yices_bvge_atom(x, e4);
  e11 = yices_ite(e5, e5, e8);
  e14 = yices_implies(e11, yices_false());
  e18 = yices_and2(e14, yices_not(yices_bveq_atom(x, yices_bvconst_uint32(5, 0))));

  code = yices_assert_formula(ctx, e18);
  if (code < 0) {
    yices_free_context(ctx);
    fail("yices_assert_formula(issue145) failed");
  }

  status = yices_check_context(ctx, NULL);
  if (status != YICES_STATUS_UNSAT) {
    yices_free_context(ctx);
    fail("expected UNSAT from issue145 trace test");
  }

  yices_free_context(ctx);
}

/*
 * Trigger path:
 * yices_check_context -> mcsat propagate (non-bool plugin)
 * -> (trace) propagation_check(...)
 */
static void test_mcsat_propagation_check_trace(void) {
  context_t *ctx;
  term_t x, x4, x_le_0, x_or_0, abs_x4, sub_t, sq_t, mul_t, arbitrary;
  term_t one, r1;
  term_t distinct_args[2];
  smt_status_t status;
  int32_t code;

  ctx = make_mcsat_context_with_trace("QF_NIA", "mcsat::propagation::check");
  if (ctx == NULL) {
    fail("failed to create mcsat context (propagation trace)");
  }

  /*
   * Non-linear arithmetic UNSAT instance adapted from nra_plugin_explain.c.
   * This tends to force non-Boolean plugin reasoning/propagation.
   */
  x = yices_new_uninterpreted_term(yices_int_type());
  x4 = yices_power(x, 4);
  x_le_0 = yices_arith_leq_atom(x, yices_zero());
  x_or_0 = yices_ite(x_le_0, x, yices_zero());
  abs_x4 = yices_abs(x4);
  sub_t = yices_sub(x4, x_or_0);
  sq_t = yices_square(sub_t);
  mul_t = yices_mul(abs_x4, sq_t);
  arbitrary = yices_mul(x_or_0, mul_t);

  one = yices_int32(1);
  r1 = yices_ite(yices_eq(yices_zero(), arbitrary), one, yices_idiv(arbitrary, arbitrary));
  distinct_args[0] = r1;
  distinct_args[1] = one;

  code = yices_assert_formula(ctx, yices_distinct(2, distinct_args));
  if (code < 0) {
    yices_free_context(ctx);
    fail("yices_assert_formula(distinct) failed");
  }

  status = yices_check_context(ctx, NULL);
  if (status != YICES_STATUS_UNSAT) {
    yices_free_context(ctx);
    fail("expected UNSAT from propagation trace test");
  }

  yices_free_context(ctx);
}

int main(void) {
  if (!yices_has_mcsat()) {
    return 1; // skipped
  }

  yices_init();

  start_deadlock_watchdog();

  test_mcsat_propagation_check_trace();
  test_mcsat_bv_conflict_trace_issue145();

  stop_deadlock_watchdog();
  yices_exit();
  return 0;
}
