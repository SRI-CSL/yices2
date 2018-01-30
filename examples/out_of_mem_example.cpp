/*
 * YICES API EXAMPLE: OUT-OF-MEM CALLBACK IN C++
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
