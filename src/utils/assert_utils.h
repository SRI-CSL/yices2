/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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


#endif /* __ASSERT_UTILS_H */
