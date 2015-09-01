/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Support for printing trace/messages depending on a verbosity level.
 */

#include <stdarg.h>
#include <errno.h>

#include "io/term_printer.h"
#include "io/tracer.h"
#include "io/type_printer.h"
#include "utils/memalloc.h"


/*
 * Allocate and initialize the pretty printer object
 */
static yices_pp_t *tracer_get_pp(tracer_t *tracer) {
  yices_pp_t *pp;

  pp = tracer->pp;
  if (pp == NULL) {
    pp = (yices_pp_t *) safe_malloc(sizeof(yices_pp_t));
    init_default_yices_pp(pp, tracer->file, NULL);
    tracer->pp = pp;
  }

  return pp;
}


/*
 * Delete the pp object if any
 */
static void tracer_delete_pp(tracer_t *tracer) {
  yices_pp_t *pp;

  pp = tracer->pp;
  if (pp != NULL) {
    delete_yices_pp(pp, false);
    safe_free(pp);
    tracer->pp = NULL;
  }
}


/*
 * Set the output file to f
 * - f must be open and writable
 * - close the current file if not equal to stderr
 */
void set_trace_file(tracer_t *tracer, FILE *f) {
  if (tracer->file != f) {
    if (tracer->file != stderr) {
      fclose(tracer->file);
    }
    tracer_delete_pp(tracer);
    tracer->file = f;
    tracer->print_failed = false;
    tracer->err_code = 0;
  }
}


/*
 * Close the file (unless it's stderr)
 */
void delete_trace(tracer_t *tracer) {
  uint32_t i;

  if (tracer->file != stderr) {
    fclose(tracer->file);
  }
  tracer_delete_pp(tracer);
  tracer->file = NULL;

  for (i = 0; i < tracer->trace_tags.size; ++ i) {
    free(tracer->trace_tags.data[i]);
  }
  delete_pvector(&tracer->trace_tags);
}



/*
 * Check whether the tracing tag has been enabled.
 * - return false if trace is NULL;
 */
bool tracing_tag(tracer_t *tracer, const char *tag) {
  uint32_t i;
  if (tracer == NULL) return false;
  for (i = 0; i < tracer->trace_tags.size; ++ i) {
    if (strcmp(tag, tracer->trace_tags.data[i]) == 0) {
      return true;
    }
  }
  return false;
}


/*
 * Print a message
 */
void tprintf(tracer_t *tracer, uint32_t level, const char *format, ...) {
  va_list p;
  int code;

  if (tracer != NULL && level <= tracer->vlevel && !tracer->print_failed) {
    va_start(p, format);
    code = vfprintf(tracer->file, format, p);
    if (code >= 0) {
      code = fflush(tracer->file);
    }
    if (code < 0) {
      tracer->print_failed = true;
      tracer->err_code = errno;
    }
    va_end(p);
  }
}

void tputs(tracer_t *tracer, uint32_t level, const char *s) {
  int code;

  if (tracer != NULL && level <= tracer->vlevel && !tracer->print_failed) {
    code = fputs(s, tracer->file);
    if (code < 0) {
      tracer->print_failed = true;
      tracer->err_code = errno;
    }
  }
}

// newline if tracer->vlevel >= level
void tnewline(tracer_t *tracer, uint32_t level) {
  int code;

  if (tracer != NULL && level <= tracer->vlevel && !tracer->print_failed) {
    code = fputc('\n', tracer->file);
    if (code < 0) {
      tracer->print_failed = true;
      tracer->err_code = errno;
    }
  }
}


/*
 * Pretty print term t + newline
 */
void tpp_term(tracer_t *tracer, uint32_t level, term_table_t *tbl, term_t t) {
  yices_pp_t *pp;

  if (tracer != NULL && level <= tracer->vlevel && !tracer->print_failed) {
    pp = tracer_get_pp(tracer);
    pp_term_full(pp, tbl, t);
    flush_yices_pp(pp);
    if (yices_pp_print_failed(pp)) {
      tracer->print_failed = true;
      tracer->err_code = yices_pp_errno(pp);
    }
  }
}


/*
 * Pretty print type tau + newline
 */
void tpp_type(tracer_t *tracer, uint32_t level, type_table_t *tbl, type_t tau) {
  yices_pp_t *pp;

  if (tracer != NULL && level <= tracer->vlevel && !tracer->print_failed) {
    pp = tracer_get_pp(tracer);
    pp_type(pp, tbl, tau);
    flush_yices_pp(pp);
    if (yices_pp_print_failed(pp)) {
      tracer->print_failed = true;
      tracer->err_code = yices_pp_errno(pp);
    }
  }
}
