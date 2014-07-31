/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/assert_utils.h"

typedef size_t tptr_t;

typedef enum tag_e {
  tag00 = 0,
  tag01 = 1,
  tag10 = 2,
  tag11 = 3,
} tag_t;

#define MAX_TAGINT (((int32_t) 1) << 29)
#define MIN_TAGINT (-MAX_TAGINT)
#define MAX_TAGUINT (((uint32_t) 1) << 30)

static inline tag_t get_tag(tptr_t p) {
  return (tag_t) (p & 0x3);
}

static inline int32_t untag_int(tptr_t p) {
  return ((int32_t) p) >> 2;
}

static inline uint32_t untag_uint(tptr_t p) {
  return ((uint32_t) p) >> 2;
}

static inline void *untag_ptr(tptr_t p) {
  return (void*) (p & ~ ((size_t) 0x3));
}

static inline tptr_t tag_ptr(void *x, tag_t tg) {
  assert((((size_t) x) & 0x3) == 0);
  return ((size_t) x) | tg;
}

static inline tptr_t tag_int(int32_t x, tag_t tg) {
  assert(MIN_TAGINT <= x && x < MAX_TAGINT);
  return (((size_t) x) << 2) | tg;
}

static inline tptr_t tag_uint(uint32_t x, tag_t tg) {
  assert(x < MAX_TAGUINT);
  return (((size_t) x) << 2) | tg;
}


static void test_int(int32_t x) {
  tptr_t p;

  printf("Test int: x = %"PRId32, x);
  p = tag_int(x, tag00);
  assert_true(get_tag(p) == tag00);
  assert_true(untag_int(p) == x);
  p = tag_int(x, tag01);
  assert_true(get_tag(p) == tag01);
  assert_true(untag_int(p) == x);
  p = tag_int(x, tag10);
  assert_true(get_tag(p) == tag10);
  assert_true(untag_int(p) == x);
  p = tag_int(x, tag11);
  assert_true(get_tag(p) == tag11);
  assert_true(untag_int(p) == x);
  printf(": OK\n");
  fflush(stdout);
}


static void test_uint(uint32_t x) {
  tptr_t p;

  printf("Test uint: x = %"PRIu32, x);
  p = tag_uint(x, tag00);
  assert_true(get_tag(p) == tag00);
  assert_true(untag_uint(p) == x);
  p = tag_uint(x, tag01);
  assert_true(get_tag(p) == tag01);
  assert_true(untag_uint(p) == x);
  p = tag_uint(x, tag10);
  assert_true(get_tag(p) == tag10);
  assert_true(untag_uint(p) == x);
  p = tag_uint(x, tag11);
  assert_true(get_tag(p) == tag11);
  assert_true(untag_uint(p) == x);
  printf(": OK\n");
  fflush(stdout);
}


static void test_ptr(void *x) {
  tptr_t p;

  printf("Test pointer: x = %p", x);
  p = tag_ptr(x, tag00);
  assert_true(get_tag(p) == tag00);
  assert_true(untag_ptr(p) == x);
  p = tag_ptr(x, tag01);
  assert_true(get_tag(p) == tag01);
  assert_true(untag_ptr(p) == x);
  p = tag_ptr(x, tag10);
  assert_true(get_tag(p) == tag10);
  assert_true(untag_ptr(p) == x);
  p = tag_ptr(x, tag11);
  assert_true(get_tag(p) == tag11);
  assert_true(untag_ptr(p) == x);
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
  a = MAX_TAGINT-2; test_int(a);
  a = MAX_TAGINT-1; test_int(a);
  a = MIN_TAGINT+2; test_int(a);
  a = MIN_TAGINT+1; test_int(a);
  a = MIN_TAGINT; test_int(a);

  b = 0; test_uint(b);
  b = 1; test_uint(b);
  b = MAX_TAGUINT-2; test_uint(b);
  b = MAX_TAGUINT-1; test_uint(b);

  c = NULL; test_ptr(c);
  c = (void *) &a; test_ptr(c);
  c = (void *) &b; test_ptr(c);
  c = (void *) &c; test_ptr(c);

  return 0;
}
