/*
 * Placeholder for the main Yices executable.
 * Right now it just prints the version.
 */

#include <stdio.h>
#include <gmp.h>

#include "yices.h"

static void print_version(void) {
  printf("Yices %s. Copyright SRI International, 2009\n"
	 "GMP %s. Copyright Free Software Foundation, Inc.\n"
	 "Build date: %s\n"
	 "Platform: %s (%s)\n",
	 yices_version, gmp_version, 
	 yices_build_date, yices_build_arch, yices_build_mode);
  fflush(stdout);
}


int main() {
  print_version();
  return 0;
}

