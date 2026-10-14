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
 * VARIANTS OF ASSERT
 *
 * In several place, we call a function that returns a Boolean result
 * and treat this result differently depending on the compilation mode:
 * - in DEBUG mode: we want to assert that the result is true
 * - in other modes, we just ignore the result.
 *
 * We could do this as follows:
 *
 *   bool check =_function(....)
 *   assert(check)
 *
 * But some compilers produce compilation warnings:
 * variable ‘check’ set but not used [-Wunused-but-set-variable]
 *
 * We define a variant of assert to fix these warnings without
 * adding ugly #ifndef NDEBUG in many places. To use it,
 * replace the code fragment above by
 *
 *    assert_true(function(....))
 * or assert_false(function(...))
 *
 * assert_always is for a condition that must hold in every mode, where going on
 * would be worse than stopping: a case that is not implemented yet and would
 * otherwise produce a wrong answer. With assertions enabled, this is a regular
 * assert, otherwise it checks the condition and leaves with YICES_EXIT_INTERNAL_ERROR.
 */

#ifndef __ASSERT_UTILS_H
#define __ASSERT_UTILS_H

#include <assert.h>
#include <stdbool.h>

static inline __attribute__ ((always_inline)) bool assert_true(bool flag) {
  assert(flag);
  return flag;
}

static inline __attribute__ ((always_inline)) bool assert_false(bool flag) {
  assert(!flag);
  return flag;
}

#ifdef NDEBUG
/*
 * Report a failed assert_always and leave. In assert_utils.c, so that this
 * header does not drag stdio, unistd and the exit codes into every user.
 */
extern void assert_always_failed(const char *file, unsigned line, const char *func, const char *cond)
  __attribute__ ((noreturn, cold));

#define assert_always(cond)                                            \
  do {                                                                 \
    if (__builtin_expect(!(cond), 0)) {                                \
      assert_always_failed(__FILE__, __LINE__, __func__, #cond);       \
    }                                                                  \
  } while (false)
#else
#define assert_always(cond) assert(cond)
#endif

#endif /* __ASSERT_UTILS_H */
