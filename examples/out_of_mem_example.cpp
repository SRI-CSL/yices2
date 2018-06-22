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
 * YICES API EXAMPLE: OUT-OF-MEMORY CALLBACK IN C++
 */

#include <assert.h>
#include <stdio.h>
#include <yices.h>

#include <new>
#include <iostream>

/*
 * Throw an exception if Yices runs out-of-memory
 */
static void out_of_mem() {
  std::bad_alloc exception;
  throw exception;
}

int main() {
  printf("Testing Yices %s (%s, %s)\n", yices_version,
	 yices_build_arch, yices_build_mode);

  yices_init();
  yices_set_out_of_mem_callback(out_of_mem);

  /*
   * Allocate new contexts until we run out of memory.
   * It's a good idea to set a memory limit before calling this program.
   */
  int n = 0;
  while (true) {
    n ++;
    try {
      yices_new_context(NULL);
    } catch (std::bad_alloc &ba) {
      std::cerr << "Out of Memory: " << ba.what() << " after " << n << " rounds\n";
      return 1;
    }
  }

  yices_exit();

  return 0;
}
