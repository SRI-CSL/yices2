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

#include <stdio.h>
#include <stdlib.h>

#include "io/reader.h"

static reader_t reader;

int main(int argc, char *argv[]) {
  char *filename;
  int c;

  if (argc <= 1) {
    init_stdin_reader(&reader);
  } else {
    filename = argv[1];
    if (init_file_reader(&reader, filename) < 0) {
      perror(filename);
      exit(2);
    }
  }

  c = reader_current_char(&reader);
  while (c != EOF) {
    c = reader_next_char(&reader);
  }

  close_reader(&reader);
  return 0;
}
