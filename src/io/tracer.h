/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Support for printing trace/messages depending on a verbosity level.
 */

#ifndef __TRACER_H
#define __TRACER_H

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

#include "io/yices_pp.h"
#include "terms/terms.h"
#include "terms/types.h"


/*
 * Tracer structure:
 * - an open FILE
 * + an optional pretty printing object
 * + a verbosity level (higher means more verbose)
 * + error codes if printing fails
 */
typedef struct tracer_s {
  FILE *file;
  yices_pp_t *pp;
  uint32_t vlevel;
  bool print_failed;     // true if printing fails
  int err_code;          // copy of errno when failure was reported
} tracer_t;


/*
 * Initialize to defaults
 */
static inline void init_trace(tracer_t *tracer) {
  tracer->file = stderr;
  tracer->pp = NULL;
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
 * Check whether the verbosity level is at least lvl
 * - return false if trace is NULL
 */
static inline bool tracing(tracer_t *tracer, uint32_t lvl) {
  return tracer != NULL && tracer->vlevel >= lvl;
}


/*
 * Change output file:
 * - f must be open and writable
 * - close the current file if it's not stderr
 * - reset the print_failed and err_code flags
 * - also close and delete the tracer->pp object if there is one
 */
extern void set_trace_file(tracer_t *tracer, FILE *f);

/*
 * Close/delete the tracer
 * - close the current file if it's not stderr
 * - close and delete the pp object if any
 */
extern void delete_trace(tracer_t *tracer);

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
extern void tprintf(tracer_t *tracer, uint32_t level, const char *format, ...)
  __attribute__ ((format (printf, 3, 4)));


/*
 * Print string s if tracer->vlevel >= level
 * (same as fputs)
 */
extern void tputs(tracer_t *tracer, uint32_t level, const char *s);


/*
 * Newline
 */
extern void tnewline(tracer_t *trace, uint32_t level);


/*
 * Pretty printing:
 * - the tracer->pp object is created and initialized on the
 *   first call to one of these functions (provided tracer->vlevle >= level)
 */

/*
 * Pretty printing of term t + newline
 * - tbl = corresponding term table
 * - use the default printing area
 */
extern void tpp_term(tracer_t *trace, uint32_t level, term_table_t *tbl, term_t t);

/*
 * Pretty printing of type tau + newline
 * - tbl = corresponding type table
 * - use the default printing area
 */
extern void tpp_type(tracer_t *traced, uint32_t level, type_table_t *tbl, type_t tau);


#endif /* __TRACER_H */
