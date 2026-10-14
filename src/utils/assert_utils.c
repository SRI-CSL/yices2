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
