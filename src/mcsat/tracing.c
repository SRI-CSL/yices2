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
 
#include "mcsat/tracing.h"
#include "io/term_printer.h"

#include <stdarg.h>
#include <errno.h>

void term_print_to_file(FILE* out, term_table_t* terms, term_t t) {
  yices_pp_t printer;
  init_yices_pp(&printer, out, NULL, PP_HMODE, 0);
  pp_term_full(&printer, terms, t);
  flush_pp(&printer.pp, false);
  delete_yices_pp(&printer, false);
}

void trace_term_ln(tracer_t* tracer, term_table_t* terms, term_t t) {
  trace_pp_term(tracer, 0, terms, t);
}

void ctx_trace_term(const plugin_context_t* ctx, term_t t) {
  trace_pp_term(ctx->tracer, 0, ctx->terms, t);
}

void ctx_trace_value(const plugin_context_t* ctx, const mcsat_value_t* value) {
  mcsat_value_print(value, ctx->tracer->file);
}

const char* kind_to_string(term_kind_t t) {
  switch (t) {
  case OR_TERM:
    return "OR_TERM";
  case XOR_TERM:
    return "XOR_TERM";
  case EQ_TERM:
    return "EQ_TERM";
  case ITE_TERM:
    return "ITE_TERM";
  case UNINTERPRETED_TERM:
    return "UNINTERPRETED_TERM";
  default:
    assert(false);
    return "UNKNOWN_TERM";
  }
}

const char* type_to_string(type_kind_t kind) {
  switch (kind) {
  case UNUSED_TYPE:
    return "UNUSED_TYPE";
  case BOOL_TYPE:
    return "BOOL_TYPE";
  case INT_TYPE:
    return "INT_TYPE";
  case REAL_TYPE:
    return "REAL_TYPE";
  case BITVECTOR_TYPE:
    return "BITVECTOR_TYPE";
  case SCALAR_TYPE:
    return "SCALAR_TYPE";
  case UNINTERPRETED_TYPE:
    return "UNINTERPRETED_TYPE";
  case VARIABLE_TYPE:
    return "VARIABLE_TYPE";
  case TUPLE_TYPE:
    return "TUPLE_TYPE";
  case FUNCTION_TYPE:
    return "FUNCTION_TYPE";
  case INSTANCE_TYPE:
    return "INSTANCE_TYPE";
  default:
    assert(false);
    return "UNKNOWN_TYPE";
  }
}

void mcsat_trace_printf(tracer_t* tracer, const char* format, ...) {
  va_list p;
  int code;

  if (tracer != NULL && !tracer->print_failed) {
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

void ctx_trace_printf(const plugin_context_t* ctx, const char* format, ...) {
  va_list p;
  int code;

  if (ctx->tracer != NULL && !ctx->tracer->print_failed) {
    va_start(p, format);
    code = vfprintf(ctx->tracer->file, format, p);
    if (code >= 0) {
      code = fflush(ctx->tracer->file);
    }
    if (code < 0) {
      ctx->tracer->print_failed = true;
      ctx->tracer->err_code = errno;
    }
    va_end(p);
  }
}
