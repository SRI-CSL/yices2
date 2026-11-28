/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * Regression test for issue #698.
 *
 * In thread-safe builds, yices_check_context_with_assumptions validated and
 * internalized its assumptions without holding the global lock. The term table
 * was therefore read (and extended) while other threads were creating terms,
 * which can crash when the table is reallocated.
 *
 * Each worker owns a private context and calls the function with a fresh
 * assumption every round, so every call creates new terms. Extra "noise"
 * threads only create terms, to make the table grow while the workers read it.
 *
 * Exit codes follow tests/api/run_test.sh: 0 = pass, 1 = skipped,
 * anything else (including a crash) = failure.
 */

#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#include <yices.h>

#if defined(_WIN32) || !defined(THREAD_SAFE)

/*
 * Skipped on Windows (the test uses pthreads) and in builds without thread
 * safety. tests/api/Makefile passes -DTHREAD_SAFE (and -pthread) only for
 * thread-safe builds, so this also avoids needing pthreads at link time.
 */
int main(void) {
  return 1;
}

#else

#include <pthread.h>
#include <signal.h>
#include <time.h>
#include <unistd.h>

/*
 * run_test.sh limits the CPU time of a test, summed over all threads.
 * Instrumented builds (coverage) can be many times slower. So every thread
 * also stops after WORK_SECONDS of wall-clock time. This bounds the CPU time
 * to about (threads * WORK_SECONDS) in any build. More noise threads find the
 * race faster than more rounds.
 */
#define NUM_WORKERS  16
#define NUM_NOISE    8
#define NUM_ROUNDS   1000
#define WORK_SECONDS 2
#define HANG_SECONDS 30

typedef struct {
  uint32_t id;
  uint32_t failures;
} worker_t;

static struct timespec deadline;
static volatile uint32_t progress[NUM_WORKERS];

static bool expired(void) {
  struct timespec now;

  clock_gettime(CLOCK_MONOTONIC, &now);
  return now.tv_sec > deadline.tv_sec ||
    (now.tv_sec == deadline.tv_sec && now.tv_nsec >= deadline.tv_nsec);
}

// A hang is a failure. Print how far each worker got.
static void on_alarm(int sig) {
  uint32_t i;

  (void) sig;
  fprintf(stderr, "timeout: possible hang; rounds done per worker:");
  for (i = 0; i < NUM_WORKERS; i++) fprintf(stderr, " %u", (unsigned) progress[i]);
  fprintf(stderr, "\n");
  _exit(3);
}

static void *worker_main(void *arg) {
  worker_t *w = (worker_t *) arg;
  ctx_config_t *config;
  context_t *ctx;
  type_t bv32;
  term_t x, sum, eq;
  uint32_t r;

  w->failures = 0;

  config = yices_new_config();
  if (yices_default_config_for_logic(config, "QF_BV") < 0) {
    yices_free_config(config);
    w->failures++;
    return NULL;
  }
  // several checks on the same context, as in the report
  yices_set_config(config, "mode", "multi-checks");
  ctx = yices_new_context(config);
  yices_free_config(config);
  if (ctx == NULL) {
    w->failures++;
    return NULL;
  }

  bv32 = yices_bv_type(32);
  x = yices_new_uninterpreted_term(bv32);

  for (r = 0; r < NUM_ROUNDS && !expired(); r++) {
    // fresh constants every round: new terms are created by each call
    sum = yices_bvadd(x, yices_bvconst_uint32(32, r));
    eq = yices_eq(sum, yices_bvconst_uint32(32, w->id * 100000 + 2 * r));
    if (yices_check_context_with_assumptions(ctx, NULL, 1, &eq) != YICES_STATUS_SAT) {
      w->failures++;
    }
    progress[w->id] = r + 1;
  }

  yices_free_context(ctx);
  return NULL;
}

static void *noise_main(void *arg) {
  uint32_t id = (uint32_t)(uintptr_t) arg;
  type_t bv32 = yices_bv_type(32);
  uint32_t i;

  // only create terms: this makes the term table grow
  for (i = 0; i < 4 * NUM_ROUNDS && !expired(); i++) {
    term_t t = yices_new_uninterpreted_term(bv32);
    (void) yices_bvadd(t, yices_bvconst_uint32(32, id * 1000000 + i));
  }
  return NULL;
}

int main(void) {
  pthread_t workers[NUM_WORKERS];
  pthread_t noise[NUM_NOISE];
  worker_t data[NUM_WORKERS];
  uint32_t i, failures;

  yices_init();

  if (!yices_is_thread_safe()) {
    yices_exit();
    return 1; // skipped: not a thread-safe build
  }

  signal(SIGALRM, on_alarm);
  alarm(HANG_SECONDS);
  clock_gettime(CLOCK_MONOTONIC, &deadline);
  deadline.tv_sec += WORK_SECONDS;

  for (i = 0; i < NUM_WORKERS; i++) {
    data[i].id = i;
    if (pthread_create(&workers[i], NULL, worker_main, &data[i]) != 0) {
      fprintf(stderr, "failed to create worker thread %u\n", i);
      return 2;
    }
  }
  for (i = 0; i < NUM_NOISE; i++) {
    if (pthread_create(&noise[i], NULL, noise_main, (void *)(uintptr_t) i) != 0) {
      fprintf(stderr, "failed to create noise thread %u\n", i);
      return 2;
    }
  }

  for (i = 0; i < NUM_WORKERS; i++) pthread_join(workers[i], NULL);
  for (i = 0; i < NUM_NOISE; i++) pthread_join(noise[i], NULL);

  failures = 0;
  for (i = 0; i < NUM_WORKERS; i++) failures += data[i].failures;

  alarm(0);
  yices_exit();

  if (failures > 0) {
    fprintf(stderr, "%u unexpected results from yices_check_context_with_assumptions\n", failures);
    return 3;
  }
  return 0;
}

#endif
