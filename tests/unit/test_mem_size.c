/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
