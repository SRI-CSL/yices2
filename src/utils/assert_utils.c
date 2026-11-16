/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * REPORTING FOR ASSERT_ALWAYS
 */

#include "assert_utils.h"

#ifdef NDEBUG
#include <inttypes.h>
#include <stdio.h>
#include <unistd.h>

#include "../include/yices_exit_codes.h"

void assert_always_failed(const char *file, unsigned line, const char *func, const char *cond) {
  // Same shape as the report of a failed assert, so the two modes read alike
  fprintf(stderr, "%s:%"PRIu32": %s: Assertion `%s' failed.\n", file, line, func, cond);
  _exit(YICES_EXIT_INTERNAL_ERROR);
}
#endif
