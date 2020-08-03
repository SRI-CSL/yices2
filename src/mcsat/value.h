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

#ifndef MCSAT_VALUE_H_
#define MCSAT_VALUE_H_

#include <stdbool.h>
#include <poly/value.h>

#include "terms/terms.h"
#include "terms/term_manager.h"
#include "terms/rationals.h"
#include "terms/bv_constants.h"
#include "model/concrete_values.h"

typedef enum {
  /** No value */
  VALUE_NONE,
  /** Boolean value */
  VALUE_BOOLEAN,
  /** A rational */
  VALUE_RATIONAL,
  /** A value from the libpoly library */
  VALUE_LIBPOLY,
  /** A bitvector value */
  VALUE_BV
} mcsat_value_type_t;

typedef struct value_s {
  mcsat_value_type_t type;
  union {
    bool b;
    rational_t q;
    lp_value_t lp_value;
    bvconstant_t bv_value;
  };
} mcsat_value_t;

/** Predefined none value for convenience */
extern const mcsat_value_t mcsat_value_none;

/** Predefined true value for convenience */
extern const mcsat_value_t mcsat_value_true;

/** Predefined false value for convenience */
extern const mcsat_value_t mcsat_value_false;

/** Construct a default value (VALUE_NONE) */
void mcsat_value_construct_default(mcsat_value_t *value);

/** Construct a boolean */
void mcsat_value_construct_bool(mcsat_value_t *value, bool b);

/** Construct a rational */
void mcsat_value_construct_rational(mcsat_value_t *value, const rational_t *q);

/** Construct a value from the libpoly value */
void mcsat_value_construct_lp_value(mcsat_value_t *value, const lp_value_t *lp_value);

/** Construct a value from the libpoly value */
void mcsat_value_construct_lp_value_direct(mcsat_value_t *value, lp_value_type_t type, void* data);

/** Construct a bv value. Passing NULL for bv_value will leave the bvconstant default-initialized. */
void mcsat_value_construct_bv_value(mcsat_value_t *value, const bvconstant_t *bv_value);

/** Construct a copy */
void mcsat_value_construct_copy(mcsat_value_t *value, const mcsat_value_t *from);

/** Construct a copy of n values */
void mcsat_value_construct_copy_n(mcsat_value_t *value, const mcsat_value_t *from, uint32_t n);

/** Construct an MCSAT value from given value */
void mcsat_value_construct_from_value(mcsat_value_t* mcsat_value, value_table_t* vtbl, value_t v);

/** Construct a value from a constant term */
void mcsat_value_construct_from_constant_term(mcsat_value_t* value, term_table_t* terms, term_t c);

/** Construct a default value (VALUE_NONE) */
mcsat_value_t* mcsat_value_new_default();

/** Construct and allocate a boolean */
mcsat_value_t* mcsat_value_new_bool(bool b);

/** Construct and allcoate a rational */
mcsat_value_t* mcsat_value_new_rational(const rational_t *q);

/** Construct and allocate a value from the libpoly value */
mcsat_value_t* mcsat_value_new_lp_value(const lp_value_t *lp_value);

/** Construct and allocate a bv value */
mcsat_value_t* mcsat_value_new_bv_value(const bvconstant_t *bv_value);

/** Construct and allocate a copy */
mcsat_value_t* mcsat_value_new_copy(const mcsat_value_t *from);

/** Destruct the value (removes any data and sets back to VALUE_NONE) */
void mcsat_value_destruct(mcsat_value_t *value);

/** Delete the value */
void mcsat_value_delete(mcsat_value_t *value);

/** Assign a value */
void mcsat_value_assign(mcsat_value_t *value, const mcsat_value_t *from);

/** Check two values for equalities */
bool mcsat_value_eq(const mcsat_value_t *v1, const mcsat_value_t *v2);

/** Get a hash of the value */
uint32_t mcsat_value_hash(const mcsat_value_t *v);

/** Print the value */
void mcsat_value_print(const mcsat_value_t *value, FILE *out);

/** Convert a basic value to yices model value. Types is passed in to enforce a type (e.g. for UF) */
value_t mcsat_value_to_value(const mcsat_value_t *value, type_table_t *types, type_t type, value_table_t *vtbl);

/** Convert a basic value to a term */
term_t mcsat_value_to_term(const mcsat_value_t *value, term_manager_t* tm);

/** Returns true if the value is 0 */
bool mcsat_value_is_zero(const mcsat_value_t *value);

/** Returns true if the value is true */
bool mcsat_value_is_true(const mcsat_value_t *value);

/** Returns true if the value is false */
bool mcsat_value_is_false(const mcsat_value_t *value);

#endif /* MCSAT_VALUE_H_ */
