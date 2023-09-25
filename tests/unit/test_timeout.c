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
 * TEST THE TIMEOUT MODULE
 */

#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/cputime.h"
#include "utils/timeout.h"


/*
 * Timeout handler: set the interrupt flag
 */
typedef struct wrapper_s {
  volatile bool interrupted;
} wrapper_t;

static wrapper_t wrapper;

static void handler(void *ptr) {
  assert(ptr == &wrapper);
  printf("     timeout received\n");
  fflush(stdout);
  ((wrapper_t *) ptr)->interrupted = true;
}


/*
 * Busy computation: increment a binary counter
 * - c = array of bits (0 or 1) in little-endian
 * - n = number of bits
 */
// increment c and return the carry out
static uint32_t increment(uint32_t *c, uint32_t n) {
  uint32_t i, c0, b;

  c0 = 1; // carry
  for (i=0; i<n; i++) {
    b = c0 + c[i];
    c[i] = b % 2;
    c0 = b/2;
  }

  return c0;
}

// increment until we get a carry out or an interrupt
static void loop(uint32_t *c, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    c[i] = 0;
  }

  do {
    i = increment(c, n);
  } while (i == 0 && !wrapper.interrupted);
}

// print the counter value
static void show_counter(uint32_t *c, uint32_t n) {
  while (n > 0) {
    n --;
    assert(c[n] == 0 || c[n] == 1);
    fputc('0' + c[n], stdout);
  }
}


/*
 * Test: n = size of the counter, t = timeout value
 */
static void test_timeout(timeout_t *to, uint32_t *c, uint32_t n, uint32_t timeout) {
  double start, end;

  printf("---> test: size = %"PRIu32", timeout = %"PRIu32" s\n", n, timeout);
  fflush(stdout);
  wrapper.interrupted  = false;
  start_timeout(to, timeout, handler, &wrapper);
  start = get_cpu_time();
  loop(c, n);
  clear_timeout(to);
  end = get_cpu_time();
  printf("     cpu time = %.2f s\n", end - start);
  fflush(stdout);
  if (wrapper.interrupted) {
    printf("     interrupted at: ");
    show_counter(c, n);
    printf("\n");
    fflush(stdout);
  } else {
    printf("     completed: ");
    show_counter(c, n);
    printf("\n");
    fflush(stdout);
  }
}


/*
 * Global array used as counter
 */
static uint32_t counter[64];

int main(void) {
  uint32_t n;
  uint32_t time;
  timeout_t *timeout;
  
  timeout = init_timeout();

  time = 20;
  for (n=5; n<40; n++) {
    test_timeout(timeout, counter, n, time);
  }

  delete_timeout(timeout);

  return 0;
}
