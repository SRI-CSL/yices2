/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef MCSAT_VARIABLE_DB_H_
#define MCSAT_VARIABLE_DB_H_

#include "io/tracer.h"
#include "terms/terms.h"
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
bool variable_db_has_variable(variable_db_t* var_db, term_t x);

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
variable_t variable_db_get_variable_if_exists(variable_db_t* var_db, term_t term);

/**
 * Returns the term associated with the variable. The variable should exist.
 */
term_t variable_db_get_term(const variable_db_t* var_db, variable_t term);


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

/** Returns the type kind of the variable */
type_kind_t variable_db_get_type_kind(const variable_db_t* var_db, variable_t x);

/**
 * Return the first frontier of variables. This does not include the variable
 * for the term itself.
 *
 * Examples:
 *
 *  x + y < 1 => { x : 1, y : 1 }
 *  x + x*y + ite(b, x, y) > 0  => { x : 2, y : 1, ite(b, x, y) : 1 }
 */
void variable_db_get_subvariables(const variable_db_t* var_db, term_t term, int_mset_t* t_vars);

/**
 * Substitute the given variable with the given substitution. As above substitution
 * will not look for the variable itself.
 *
 * Examples:
 *
 *  b, with b -> false => b
 *  not b, with b -> false => true
 *  x + y < 1, with x + y < 1 -> false => x + y < 1
 *  x + y < 1, with x -> y => 2y < 1
 *  x + x*y + ite(b, x, y) > 0, with x -> y => y + y^2 + ite(b, x, y) > 0
 */
term_t variable_db_substitute_subvariable(const variable_db_t* var_db,
    term_t t, variable_t x, term_t subst);

/**
 * Collect all the unused variables for reuse.
 */
void variable_db_gc_sweep(variable_db_t* var_db, gc_info_t* gc_vars);

/** Prints a variable */
void variable_db_print_variable(const variable_db_t* var_db, variable_t x, FILE* out);

/** Prints the variable database */
void variable_db_print(const variable_db_t* var_db, FILE* out);

/** Check if a valid variable */
bool variable_db_is_variable(const variable_db_t* var_db, variable_t var, bool assert);

#endif /* MCSAT_VARIABLE_DB_H_ */
