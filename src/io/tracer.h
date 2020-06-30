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
  pvector_t trace_tags;  // list of tags
  pp_lang_t lang;        // output language
} tracer_t;


/*
 * Initialize to defaults
 */
static inline void init_trace(tracer_t *tracer, pp_lang_t lang) {
  tracer->file = stderr;
  tracer->pp = NULL;
  tracer->vlevel = 0;
  tracer->print_failed = false;
  tracer->err_code = 0;
  tracer->lang = lang;
  init_pvector(&tracer->trace_tags, 5);
}


/*
 * Set verbosity level
 */
static inline void set_trace_vlevel(tracer_t *tracer, uint32_t level) {
  tracer->vlevel = level;
}

/*
 * Enable a tag to trace.
 */
static inline void enable_trace_tag(tracer_t *tracer, const char* tag) {
  pvector_push(&tracer->trace_tags, strdup(tag));
}

/*
 * Check whether the verbosity level is at least lvl
 * - return false if trace is NULL
 */
static inline bool tracing(tracer_t *tracer, uint32_t lvl) {
  return tracer != NULL && tracer->vlevel >= lvl;
}

/*
 * Check whether the tracing tag has been enabled.
 * - return false if trace is NULL;
 */
bool tracing_tag(tracer_t *tracer, const char *tag);

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
 * - both trace_printf and trace_puts call fflush
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
extern void trace_printf(tracer_t *tracer, uint32_t level, const char *format, ...)
  __attribute__ ((format (printf, 3, 4)));


/*
 * Print string s if tracer->vlevel >= level
 * (same as fputs)
 */
extern void trace_puts(tracer_t *tracer, uint32_t level, const char *s);


/*
 * Newline
 */
extern void trace_newline(tracer_t *trace, uint32_t level);


/*
 * Pretty printing:
 * - the tracer->pp object is created and initialized on the
 *   first call to one of these functions (provided tracer->vlevel >= level)
 */

/*
 * Pretty printing of term t + newline
 * - tbl = corresponding term table
 * - use the default printing area
 */
extern void trace_pp_term(tracer_t *trace, uint32_t level, term_table_t *tbl, term_t t);

/*
 * Pretty printing of type tau + newline
 * - tbl = corresponding type table
 * - use the default printing area
 */
extern void trace_pp_type(tracer_t *traced, uint32_t level, type_table_t *tbl, type_t tau);


#endif /* __TRACER_H */
