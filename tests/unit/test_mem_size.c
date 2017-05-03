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
 * Test mem_size function
 */

#include <stdio.h>

#include "utils/memalloc.h"
#include "utils/memsize.h"

int main(void) {
  double size;
  void *ptr;

  size = mem_size() / (1024 * 1024);
  printf("Initial memory use = %.2f MB\n", size);

  ptr = safe_malloc(4096 * 1024); // 4 MB?
  size = mem_size() / (1024 * 1024);
  printf("Memory use after malloc = %.2f MB\n", size);

  safe_free(ptr);
  size = mem_size() / (1024 * 1024);
  printf("Memory use after free = %.2f MB\n", size);

  return 0;
}
