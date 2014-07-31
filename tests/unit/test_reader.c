/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
