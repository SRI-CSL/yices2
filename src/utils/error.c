/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2023 SRI International.
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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "yices_exit_codes.h"

void perror_fatal(const char *s) {
  perror_fatal(s, errno);
  exit(YICES_EXIT_INTERNAL_ERROR);
}

void perror_fatal_code(const char *s, int err) {
  char buffer[64];
  
  strerror_r(err, buffer, sizeof(buffer));
  fprintf(stderr, "%s: %s\n", s, buffer);
  exit(YICES_EXIT_INTERNAL_ERROR);
}
