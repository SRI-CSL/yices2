/*
 * Support for printing trace/messages depending on a verbosity level.
 */

#ifndef __TRACER_H
#define __TRACER_H

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>


/*
 * Tracer structure:
 * - an open FILE
 * + a verbosity level (higher means more verbose)
 * + error codes if printing fails
 */
typedef struct tracer_s {
  FILE *file;
  uint32_t vlevel;
  bool print_failed;  // true if printing fails
  int err_code;          // copy of errno when failure was reported
} tracer_t;


/*
 * Initialize to defaults
 */
static inline void init_trace(tracer_t *tracer) {
  tracer->file = stderr;
  tracer->vlevel = 0;
  tracer->print_failed = false;
  tracer->err_code = 0;
}


/*
 * Set verbosity level
 */
static inline void set_trace_vlevel(tracer_t *tracer, uint32_t level) {
  tracer->vlevel = level;
}


/*
 * Change output file:
 * - f must be open and writable
 * - close the current file if it's not stderr
 * - reset the print_failed and err_code flags
 */
extern void set_trace_file(tracer_t *tracer, FILE *f);


/*
 * Close the trace file (if not stderr)
 * - no operation can be performed after this
 */
extern void close_trace(tracer_t *tracer);


/*
 * Output functions:
 * - if tracer is NULL, they do nothing
 * - otherwise, they print stuff to tracer->file provided 
 *   tracer->vlevel >= level
 * - both tprintf and tputs call fflush
 *
 * - if the output fails then tracer->print_failed is set to true
 *   and tracer->err_code is set to errno
 */

/*
 * Formatted output (as in fprintf)
 * - level = verbosity
 * - fmt = a format string as in printf
 * - rest = stuff to print (as in prinf too)
 */
extern void tprintf(tracer_t *tracer, uint32_t level, const char *format, ...);


/*
 * Print string s if tracer->vlevel >= level
 * (same as fputs)
 */
extern void tputs(tracer_t *tracer, uint32_t level, const char *s);



#endif /* __TRACER_H */
