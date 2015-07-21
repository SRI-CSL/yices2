/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef TRACING_H_
#define TRACING_H_

#include "mcsat/plugin.h"
#include <stdio.h>

/** Check if the tag is enabled */
static inline
bool ctx_trace_enabled(plugin_context_t* ctx, const char* tag) {
#ifndef NDEBUG
  return (ctx->tracer != NULL && tracing_tag(ctx->tracer, tag));
#else
  return false;
#endif
}

/** Check if the tag is enabled */
static inline
bool trace_enabled(tracer_t* tracer, const char* tag) {
#ifndef NDEBUG
  return (tracer != NULL && tracing_tag(tracer, tag));
#else
  return false;
#endif
}

/** Return the file associated with the trace */
static inline
FILE* ctx_trace_out(plugin_context_t* ctx) {
  if (ctx->tracer != NULL && ctx->tracer->file != NULL) {
    return ctx->tracer->file;
  } else {
    return stderr;
  }
}

/** Return the file associated with the trace */
static inline
FILE* trace_out(tracer_t* tracer) {
  if (tracer != NULL && tracer->file != NULL) {
    return tracer->file;
  } else {
    return stderr;
  }
}

/** Print the term to a file */
void term_print_to_file(FILE* out, term_table_t* terms, term_t t);

/** Print the term to the trace (with newline) */
void trace_term_ln(tracer_t* tracer, term_table_t* terms, term_t t);

/** Print the term to the trace */
void ctx_trace_term(plugin_context_t* ctx, term_t t);

/** Print to the trace */
void trace_printf(tracer_t* tracer, const char* format, ...) __attribute__ ((format (printf, 2, 3)));

/** Print to the trace */
void ctx_trace_printf(plugin_context_t* ctx, const char* format, ...) __attribute__ ((format (printf, 2, 3)));

/** String representation of the kind */
const char* kind_to_string(term_kind_t kind);

/** String representation of the type */
const char* type_to_string(type_kind_t kind);

#endif /* TRACING_H_ */
