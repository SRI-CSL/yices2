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
 
#ifndef TRACING_H_
#define TRACING_H_

#include "mcsat/plugin.h"
#include <stdio.h>

/** Check if the tag is enabled */
static inline
bool ctx_trace_enabled(const plugin_context_t* ctx, const char* tag) {
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
FILE* ctx_trace_out(const plugin_context_t* ctx) {
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
void ctx_trace_term(const plugin_context_t* ctx, term_t t);

/** Print the value to the trace */
void ctx_trace_value(const plugin_context_t* ctx, const mcsat_value_t* value);

/** Print to the trace */
void mcsat_trace_printf(tracer_t* tracer, const char* format, ...) __attribute__ ((format (printf, 2, 3)));

/** Print to the trace */
void ctx_trace_printf(const plugin_context_t* ctx, const char* format, ...) __attribute__ ((format (printf, 2, 3)));

/** String representation of the kind */
const char* kind_to_string(term_kind_t kind);

/** String representation of the type */
const char* type_to_string(type_kind_t kind);

#endif /* TRACING_H_ */
