/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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


#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <inttypes.h>

#include "thread_macros.h"
#include "threadsafe.h"
#include "yices.h"
#include "yices_locks.h"
#include "api/yices_globals.h"
#include "io/type_printer.h"
#include "io/term_printer.h"

#include "terms/bv64_constants.h"

/*
 * Print the type table
 */

static void show_types(FILE* output) {
  fprintf(output, "\n---- Type table ----\n");
  pp_type_table(output, __yices_globals.types);
}
void show_types_mt(FILE* output) {
  MT_PROTECT_VOID( __yices_globals.lock, show_types(output));
}


/*
 * Print the term table
 */
static void show_terms(FILE* output) {
  fprintf(output, "\n---- Term table -----\n");
  pp_term_table(output, __yices_globals.terms);
}
void show_terms_mt(FILE* output) {
  MT_PROTECT_VOID(__yices_globals.lock, show_terms(output));
}

/*
 * Predicate: check whether t has type tau
 */
static bool has_type(type_t tau, term_t t) {
  return (term_type(__yices_globals.terms, t) == tau);
}
bool has_type_mt(type_t tau, term_t t) {
  MT_PROTECT(bool,  __yices_globals.lock, has_type(tau, t));
}

static void _o_print_term(FILE* output, term_t t){
  print_term(output, __yices_globals.terms, t);
}
void print_term_mt(FILE* output, term_t t){
  MT_PROTECT_VOID(__yices_globals.lock, _o_print_term(output, t));
}

static void _o_print_type(FILE* output, type_t t){
  print_type(output, __yices_globals.types, t);
}
void print_type_mt(FILE* output, type_t t){
  MT_PROTECT_VOID(__yices_globals.lock, _o_print_type(output, t));
}

uint32_t term_bitsize_mt(term_table_t *table, term_t t) {
  MT_PROTECT(uint32_t,  __yices_globals.lock, term_bitsize(table, t));
}

static bool is_bvtype(type_t tau) {
  return (type_kind(__yices_globals.types, tau) == BITVECTOR_TYPE);
}
bool is_bvtype_mt(type_t tau) {
  MT_PROTECT(bool,  __yices_globals.lock, is_bvtype(tau));
}


/////

/*
 * Check that descriptor of a type tau matches what's expected
 */
static bool check_bool_type(type_t tau) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == BOOL_TYPE;
}
bool check_bool_type_mt(type_t tau) {
  MT_PROTECT(bool, __yices_globals.lock, check_bool_type(tau));
}

static bool check_int_type(type_t tau) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == INT_TYPE;
}
bool check_int_type_mt(type_t tau) {
  MT_PROTECT(bool, __yices_globals.lock, check_int_type(tau));
}

static bool check_real_type(type_t tau) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == REAL_TYPE;
}
bool check_real_type_mt(type_t tau) {
  MT_PROTECT(bool, __yices_globals.lock, check_real_type(tau));
}

static bool check_uninterpreted_type(type_t tau) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == UNINTERPRETED_TYPE;
}
bool check_uninterpreted_type_mt(type_t tau) {
  MT_PROTECT(bool, __yices_globals.lock, check_uninterpreted_type(tau));
}

static bool check_bv_type(type_t tau, uint32_t n) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == BITVECTOR_TYPE
    && bv_type_size(__yices_globals.types, tau) == n;
}
bool check_bv_type_mt(type_t tau, uint32_t n) {
  MT_PROTECT(bool, __yices_globals.lock, check_bv_type(tau, n));
}

static bool check_scalar_type(type_t tau, uint32_t n) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == SCALAR_TYPE
    && scalar_type_cardinal(__yices_globals.types, tau) == n;
}
bool check_scalar_type_mt(type_t tau, uint32_t n) {
  MT_PROTECT(bool, __yices_globals.lock, check_scalar_type(tau, n));
}

static bool check_tuple_type(type_t tau, uint32_t n, type_t comp[]) {
  tuple_type_t *d;
  uint32_t i;

  if (tau < 0 || type_kind(__yices_globals.types, tau) != TUPLE_TYPE) {
    return false;
  }

  d = tuple_type_desc(__yices_globals.types, tau);
  if (d->nelem != n) {
    return false;
  }

  for (i=0; i<n; i++) {
    if (d->elem[i] != comp[i]) return false;
  }

  return true;
}
bool check_tuple_type_mt(type_t tau, uint32_t n, type_t comp[]) {
  MT_PROTECT(bool, __yices_globals.lock, check_tuple_type(tau, n, comp));
}

static bool check_function_type(type_t tau, uint32_t n, type_t dom[], type_t range) {
  function_type_t *d;
  uint32_t i;

  if (tau < 0 || type_kind(__yices_globals.types, tau) != FUNCTION_TYPE) {
    return false;
  }

  d = function_type_desc(__yices_globals.types, tau);
  if (d->ndom != n || d->range != range) {
    return false;
  }

  for (i=0; i<n; i++) {
    if (d->domain[i] != dom[i]) return false;
  }

  return true;
}
bool check_function_type_mt(type_t tau, uint32_t n, type_t dom[], type_t range) {
  MT_PROTECT(bool, __yices_globals.lock, check_function_type(tau, n, dom, range));
}


/*
 * Check whether the name of type tau matches 'name'
 */
static bool check_type_name(type_t tau, const char *name) {
  char *s;

  s = type_name(__yices_globals.types, tau);
  if (name == NULL) {
    return s == NULL;
  } else {
    return s != NULL && strcmp(s, name) == 0;
  }
}
bool check_type_name_mt(type_t tau, const char *name) {
  MT_PROTECT(bool, __yices_globals.lock, check_type_name(tau, name));
}



/*
 * Check whether tau is NULL_TYPE and whether the
 * error report is what's expected.
 */
static bool check_pos_int_required(type_t tau) {
  error_report_t *rep;

  rep = yices_error_report();
  return tau == NULL_TYPE && yices_error_code() == POS_INT_REQUIRED && rep->badval <= 0;
}
bool check_pos_int_required_mt(type_t tau) {
  MT_PROTECT(bool, __yices_globals.lock, check_pos_int_required(tau));
}

static bool check_max_bvsize_exceeded(type_t tau, int64_t size) {
  error_report_t *rep;

  rep = yices_error_report();
  return tau == NULL_TYPE && yices_error_code() == MAX_BVSIZE_EXCEEDED &&
    rep->badval == size && size > (int64_t) YICES_MAX_BVSIZE;
}
bool check_max_bvsize_exceeded_mt(type_t tau, int64_t size) {
  MT_PROTECT(bool, __yices_globals.lock, check_max_bvsize_exceeded(tau, size));
}

static bool check_too_many_arguments(type_t tau, int64_t n) {
  error_report_t *rep;

  rep = yices_error_report();
  return tau == NULL_TYPE && yices_error_code() == TOO_MANY_ARGUMENTS &&
    rep->badval == n && n > (int64_t) YICES_MAX_ARITY;
}
bool check_too_many_arguments_mt(type_t tau, int64_t n) {
  MT_PROTECT(bool, __yices_globals.lock, check_too_many_arguments(tau, n));
}

static bool check_invalid_type(type_t tau, type_t bad) {
  error_report_t *rep;
  
  rep = yices_error_report();
  return tau == NULL_TYPE && bad_type(__yices_globals.types, rep->type1) && rep->type1 == bad;
}
bool check_invalid_type_mt(type_t tau, type_t bad) {
  MT_PROTECT(bool, __yices_globals.lock, check_invalid_type(tau, bad));
}


/*
 * Check that a term descriptor matches what's expected
 */
static bool check_constant_term(term_t t, type_t tau, int32_t idx) {
  return t >= 0 && is_pos_term(t) &&
    term_kind(__yices_globals.terms, t) == CONSTANT_TERM &&
    term_type(__yices_globals.terms, t) == tau &&
    constant_term_index(__yices_globals.terms, t) == idx;
}
bool check_constant_term_mt(term_t t, type_t tau, int32_t idx) {
  MT_PROTECT(bool, __yices_globals.lock, check_constant_term(t, tau, idx));
}

static bool check_uninterpreted_term(term_t t, type_t tau) {
  return t >= 0 && is_pos_term(t) &&
    term_kind(__yices_globals.terms, t) == UNINTERPRETED_TERM &&
    term_type(__yices_globals.terms, t) == tau;
}
bool check_uninterpreted_term_mt(term_t t, type_t tau) {
  MT_PROTECT(bool, __yices_globals.lock, check_uninterpreted_term(t, tau));
}


/*
 * CHECKS ON UNIT-TYPE REPRESENTATIVES
 */

static bool check_unit_tuple(term_t t, type_t tau);


static bool check_unit_rep(term_t t, type_t tau) {
  if (is_function_type(__yices_globals.types, tau)) {
    return check_uninterpreted_term(t, tau);
  } else if (is_scalar_type(__yices_globals.types, tau)) {
    return check_constant_term(t, tau, 0);
  } else {
    assert(is_tuple_type(__yices_globals.types, tau));
    return check_unit_tuple(t, tau);
  }
}
bool check_unit_rep_mt(term_t t, type_t tau) {
  MT_PROTECT(bool, __yices_globals.lock, check_unit_rep(t, tau));
}

static bool check_unit_tuple(term_t t, type_t tau) {
  tuple_type_t *d;
  composite_term_t *c;
  uint32_t i, n;

  if (t < 0 || is_neg_term(t) ||
      term_kind(__yices_globals.terms, t) != TUPLE_TERM ||
      term_type(__yices_globals.terms, t) != tau) {
    return false;
  }

  d = tuple_type_desc(__yices_globals.types, tau);
  c = tuple_term_desc(__yices_globals.terms, t);
  if (d->nelem != c->arity) {
    return false;
  }

  n = d->nelem;
  for (i=0; i<n; i++) {
    if (! check_unit_rep(c->arg[i], d->elem[i])) {
      return false;
    }
  }

  return true;
}
bool check_unit_tuple_mt(term_t t, type_t tau) {
  MT_PROTECT(bool, __yices_globals.lock, check_unit_tuple(t, tau));
}



/*
 * Error codes for constant & uninterpreted term constructors
 */
static bool check_invalid_type2(term_t t, type_t tau) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == INVALID_TYPE && rep->type1 == tau;
}
bool check_invalid_type2_mt(term_t t, type_t tau) {
  MT_PROTECT(bool, __yices_globals.lock, check_invalid_type2(t, tau));
}

static bool check_scalar_or_utype_required(term_t t, type_t tau) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == SCALAR_OR_UTYPE_REQUIRED && rep->type1 == tau;
}
bool check_scalar_or_utype_required_mt(term_t t, type_t tau) {
  MT_PROTECT(bool, __yices_globals.lock, check_scalar_or_utype_required(t, tau));
}


/*
 * ARITHMETIC CONSTANTS
 */
static bool check_arith_constant(term_t t, rational_t *q) {
  type_t tau;

  if (t < 0 || is_neg_term(t) ||
      term_kind(__yices_globals.terms, t) != ARITH_CONSTANT ||
      q_neq(rational_term_desc(__yices_globals.terms, t), q)) {
    return false;
  }

  tau = term_type(__yices_globals.terms, t);
  return q_is_integer(q) ? is_integer_type(tau) : is_real_type(tau);
}
bool check_arith_constant_mt(term_t t, rational_t *q) {
  MT_PROTECT(bool, __yices_globals.lock, check_arith_constant(t, q));
}


/*
 * BIT-VECTOR CONSTANTS
 */
static bool check_bv64_constant(term_t t, uint64_t v, uint32_t n) {
  bvconst64_term_t *c;
  type_t tau;

  if (t < 0 || is_neg_term(t) || term_kind(__yices_globals.terms, t) != BV64_CONSTANT) {
    return false;
  }

  tau = term_type(__yices_globals.terms, t);
  c = bvconst64_term_desc(__yices_globals.terms, t);
  v = norm64(v, n);

  return c->bitsize == n && c->value == v && check_bv_type(tau, n);
}
bool check_bv64_constant_mt(term_t t, uint64_t v, uint32_t n) {
  MT_PROTECT(bool, __yices_globals.lock, check_bv64_constant(t, v, n));
}


static bool check_bv_constant(term_t t, uint32_t *v, uint32_t n) {
  bvconst_term_t *c;
  type_t tau;

  if (t < 0 || is_neg_term(t) || term_kind(__yices_globals.terms, t) != BV_CONSTANT) {
    return false;
  }

  tau = term_type(__yices_globals.terms, t);
  c = bvconst_term_desc(__yices_globals.terms, t);
  bvconst_normalize(v, n);

  return c->bitsize == n && bvconst_eq(c->data, v, (n + 31)>>5) && check_bv_type(tau, n);
}
bool check_bv_constant_mt(term_t t, uint32_t *v, uint32_t n) {
  MT_PROTECT(bool, __yices_globals.lock, check_bv_constant(t, v, n));
}


