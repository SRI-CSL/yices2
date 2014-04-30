/*
 * Print_trace:
 * - shows the stack if we have support for execinfo/backtrace_symbols.
 * - no op otherwise
 */

#ifdef HAVE_BACKTRACE

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <execinfo.h>

void print_trace(void) {
  void *array[10];
  size_t size;
  char **strings;
  size_t i;
  size = backtrace (array, 10);
  strings = backtrace_symbols (array, size);
  fprintf (stderr, "Obtained %zd stack frames.\n", size);
  for (i = 0; i < size; i++)
    fprintf (stderr, "%s\n", strings[i]);
  free (strings);
} 

#else

// not supported
void print_trace(void) {
}

#endif
