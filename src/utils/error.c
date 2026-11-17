/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "yices_exit_codes.h"

void perror_fatal(const char *s) {
  perror(s);
  exit(YICES_EXIT_INTERNAL_ERROR);
}

void perror_fatal_code(const char *s, int err) {
  char buffer[64];
  
#ifdef MINGW
  fprintf(stderr, "%s: %s\n", s, strerror(err));
#else
  strerror_r(err, buffer, sizeof(buffer));
  fprintf(stderr, "%s: %s\n", s, buffer);
#endif

  exit(YICES_EXIT_INTERNAL_ERROR);
}
