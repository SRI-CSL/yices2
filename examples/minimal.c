/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
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
 * YICES API: MINIMAL EXAMPLE
 */

#include <assert.h>
#include <stdio.h>

#include <yices.h>

int main(void) {
  context_t *ctx;

  printf("Testing Yices %s (%s, %s)\n", yices_version,
	 yices_build_arch, yices_build_mode);

  yices_init();
  ctx = yices_new_context(NULL);
  yices_free_context(ctx);
  yices_exit();

  return 0;
}
