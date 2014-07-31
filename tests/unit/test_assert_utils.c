/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of assert_true function:
 * - in assert_true(test_function("aaaa'))
 *   we want test_function to be called whether or not assertions are enabled
 *   (i.e., NDEBUG defined or not)
 */

#include <stdio.h>
#include "utils/assert_utils.h"

static bool good_function(const char *msg) {
  printf("good_function called with %s\n", msg);
  fflush(stdout);

  return true;
}

static bool bad_function(const char *msg) {
  printf("bad_function called with %s\n", msg);
  fflush(stdout);

  return false;
}

int main(void) {
  assert_true(good_function("should pass"));
  assert_false(bad_function("should pass"));
  assert_true(bad_function("should_fail in DEBUG mode"));
  return true;
}
