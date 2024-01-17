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
 
#ifndef MCSAT_VARIABLE_DB_H_
#define MCSAT_VARIABLE_DB_H_

#include "io/tracer.h"
#include "terms/terms.h"
#include "terms/term_manager.h"
#include "utils/ptr_vectors.h"
#include "utils/int_vectors.h"
#include "utils/int_hash_map.h"

#include "mcsat/utils/int_mset.h"
#include "mcsat/gc.h"

typedef int32_t variable_t;

#define variable_null 0

struct variable_db_s {

  /** The term table we're using */
  term_table_t* terms;

  /** The type table we're using */
  type_table_t* types;

  /** Tracer */
  tracer_t* tracer;

  /** Map from variables to their terms */
  ivector_t variable_to_term_map;

  /** Map from terms to their variables */
  int_hmap_t term_to_variable_map;

  /** Notifications for new variables */
  pvector_t notify_new_variable;

  /** Free list */
  ivector_t free_list;
};

typedef struct variable_db_s variable_db_t;

/** Construct a new variable database */
void variable_db_construct(variable_db_t* var_db, term_table_t* terms, type_table_t* types, tracer_t* tracer);

/** Destruct the variable database */
void variable_db_destruct(variable_db_t* var_db);

/** Set the tracer */
void variable_db_set_tracer(variable_db_t* var_db, tracer_t* tracer);

/** Returns true if the term has the variable associated with it */
bool variable_db_has_variable(const variable_db_t* var_db, term_t x);

/**
 * Returns a variable associated with the term. If no variable exists, it will
 * be added and all registered listeners will be notified. Don't call on
 * negated variables.
 */
variable_t variable_db_get_variable(variable_db_t* var_db, term_t term);

/**
 * Returns a variable associated with the term. If no variable exists, it
 * returns variable_null.
 */
variable_t variable_db_get_variable_if_exists(const variable_db_t* var_db, term_t term);

/**
 * Returns the term associated with the variable. The variable should exist.
 */
static inline
term_t variable_db_get_term(const variable_db_t* var_db, variable_t x) {
  assert(x > 0 && x < var_db->variable_to_term_map.size);
  return var_db->variable_to_term_map.data[x];
}

static inline
type_t variable_db_get_type(const variable_db_t* var_db, variable_t x) {
  term_t t = variable_db_get_term(var_db, x);
  return term_type(var_db->terms, t);
}

typedef struct variable_db_new_variable_notify_s {
  void (*new_variable) (struct variable_db_new_variable_notify_s* self, variable_t x);
} variable_db_new_variable_notify_t;

/** Add a new listener for new variables */
void variable_db_add_new_variable_listener(variable_db_t* var_db, variable_db_new_variable_notify_t* listener);

/** Returns the total number of variables in the database */
uint32_t variable_db_size(const variable_db_t* var_db);

/** Returns true if the type of the variable is Boolean */
bool variable_db_is_boolean(const variable_db_t* var_db, variable_t x);

/** Returns true if the type of the variable is real */
bool variable_db_is_int(const variable_db_t* var_db, variable_t x);

/** Returns true if the type of the variable is integer */
bool variable_db_is_real(const variable_db_t* var_db, variable_t x);

/** Returns true if the type of the variable is bitvector */
bool variable_db_is_bitvector(const variable_db_t* var_db, variable_t x);

/** Returns true if the type of the variable is finite field */
bool variable_db_is_finitefield(const variable_db_t* var_db, variable_t x);

/** Get the bitsize of a bit-vector variable */
uint32_t variable_db_get_bitsize(const variable_db_t* var_db, variable_t x);

/** Returns the type kind of the variable */
type_kind_t variable_db_get_type_kind(const variable_db_t* var_db, variable_t x);

/**
 * Collect all the unused variables for reuse.
 */
void variable_db_gc_sweep(variable_db_t* var_db, gc_info_t* gc_vars);

/** Prints a variable */
void variable_db_print_variable(const variable_db_t* var_db, variable_t x, FILE* out);

/** Prints a null-terminated list of variables */
void variable_db_print_variables(const variable_db_t* var_db, const variable_t* x, FILE* out);

/** Prints the variable database */
void variable_db_print(const variable_db_t* var_db, FILE* out);

/** Check if a valid variable */
bool variable_db_is_variable(const variable_db_t* var_db, variable_t var, bool assert);

#endif /* MCSAT_VARIABLE_DB_H_ */
