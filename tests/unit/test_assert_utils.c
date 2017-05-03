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
