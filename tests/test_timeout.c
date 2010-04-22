/*
 * TEST THE TIMEOUT MODULE
 */

#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

#include "cputime.h"
#include "timeout.h"


/*
 * Timeout handler: set the interrupt flag
 */
static volatile bool interrupted;

static void handler(bool *flag) {
  assert(flag == &interrupted);
  printf("     timeout received\n");
  fflush(stdout);
  *flag = true;
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
  } while (i == 0 && !interrupted);
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
static void test_timeout(uint32_t *c, uint32_t n, uint32_t timeout) {
  double start, end;

  printf("---> test: size = %"PRIu32", timeout = %"PRIu32" s\n", n, timeout);
  interrupted  = false;
  start_timeout(timeout, (timeout_handler_t) handler, &interrupted);
  start = get_cpu_time();
  loop(c, n);
  clear_timeout();
  end = get_cpu_time();
  printf("     cpu time = %.2f s\n", end - start);
  if (interrupted) {
    printf("     interrupted at: ");
    show_counter(c, n);
    printf("\n");
  } else {
    printf("     completed: ");
    show_counter(c, n);
    printf("\n");
  }
}


/*
 * Global array used as counter
 */
static uint32_t counter[64];

int main() {
  uint32_t n;
  uint32_t time;

  init_timeout();

  time = 20;
  for (n=5; n<40; n++) {
    test_timeout(counter, n, time);
  }

  delete_timeout();

  return 0;
}
