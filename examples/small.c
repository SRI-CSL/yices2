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
