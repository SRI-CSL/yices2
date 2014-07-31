/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of the tag/untag functions in tagged_pointers.h
 */

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/tagged_pointers.h"

#define MAX_TAG_INT (INT32_MAX>>1)
#define MIN_TAG_INT (INT32_MIN>>1)
#define MAX_TAG_UINT (UINT32_MAX>>1)

static void test_int(int32_t x) {
  void *p;

  printf("Test int: x = %"PRId32, x);
  p = tag_i32(x);
  printf(", tagged: %p, untagged: %"PRId32, p, untag_i32(p));
  assert(has_int_tag(p));
  assert(untag_i32(p) == x);
  printf(": OK\n");
  fflush(stdout);
}


static void test_uint(uint32_t x) {
  void *p;

  printf("Test uint: x = %"PRIu32, x);
  p = tag_u32(x);
  printf(", tagged: %p, untagged: %"PRIu32, p, untag_u32(p));
  assert(has_int_tag(p));
  assert(untag_u32(p) == x);
  printf(": OK\n");
  fflush(stdout);
}

static void test_ptr(void *x) {
  printf("Test pointer: x = %p", x);
  assert(!has_int_tag(x));
  printf(": OK\n");
  fflush(stdout);
}


int main() {
  int32_t a;
  uint32_t b;
  void *c;

  a = 0; test_int(a);
  a = -1; test_int(a);
  a = 1; test_int(a);
  a = -2; test_int(a);
  a = 2; test_int(a);
  a = MAX_TAG_INT-2; test_int(a);
  a = MAX_TAG_INT-1; test_int(a);
  a = MAX_TAG_INT; test_int(a);
  a = MIN_TAG_INT+2; test_int(a);
  a = MIN_TAG_INT+1; test_int(a);
  a = MIN_TAG_INT; test_int(a);

  b = 0; test_uint(b);
  b = 1; test_uint(b);
  b = 2; test_uint(b);
  b = MAX_TAG_UINT-2; test_uint(b);
  b = MAX_TAG_UINT-1; test_uint(b);
  b = MAX_TAG_UINT; test_uint(b);

  c = NULL; test_ptr(c);
  c = (void *) &a; test_ptr(c);
  c = (void *) &b; test_ptr(c);
  c = (void *) &c; test_ptr(c);

  return 0;
}
