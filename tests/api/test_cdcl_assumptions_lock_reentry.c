/*
 * Regression test for lock reentry in CDCL(T) check-with-assumptions path.
 *
 * Under THREAD_SAFE pre-fix code, yices_check_context_with_assumptions held the
 * global lock, then CDCL(T) solving could reach egraph_final_check, which tried
 * to take the same global lock again.
 */

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

static context_t *make_cdclt_context(void) {
  ctx_config_t *config;
  context_t *context;
  int32_t code;

  config = yices_new_config();
  code = yices_default_config_for_logic(config, "QF_UF");
  if (code < 0) {
    yices_free_config(config);
    return NULL;
  }

  context = yices_new_context(config);
  yices_free_config(config);
  return context;
}

static void test_cdclt_check_with_assumptions_no_deadlock(void) {
  context_t *ctx;
  type_t u_ty;
  term_t a, b;
  term_t eq_ab;
  term_t assumptions[1];
  smt_status_t status;
  int32_t code;

  ctx = make_cdclt_context();
  if (ctx == NULL) {
    fail("failed to create CDCL(T) context");
  }

  u_ty = yices_new_uninterpreted_type();
  a = yices_new_uninterpreted_term(u_ty);
  b = yices_new_uninterpreted_term(u_ty);
  eq_ab = yices_eq(a, b);

  /*
   * SAT EUF instance with an assumption.
   * This exercises the CDCL(T) final-check path through egraph_final_check.
   */
  code = yices_assert_formula(ctx, eq_ab);
  if (code < 0) {
    yices_free_context(ctx);
    fail("yices_assert_formula(eq_ab) failed");
  }

  assumptions[0] = eq_ab;
  status = yices_check_context_with_assumptions(ctx, NULL, 1, assumptions);
  if (status != YICES_STATUS_SAT) {
    yices_free_context(ctx);
    fail("expected SAT from yices_check_context_with_assumptions");
  }

  yices_free_context(ctx);
}

int main(void) {
  yices_init();

  start_deadlock_watchdog();
  test_cdclt_check_with_assumptions_no_deadlock();
  stop_deadlock_watchdog();

  yices_exit();
  return 0;
}
