/*
 * Test mem_size function
 */

#include <stdio.h>

#include "memsize.h"
#include "memalloc.h"

int main() {
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
