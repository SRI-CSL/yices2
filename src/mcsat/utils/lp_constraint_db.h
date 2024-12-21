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

#ifndef LP_CONSTRAINT_DB_H
#define LP_CONSTRAINT_DB_H

#include <stdbool.h>
#include <stdio.h>

#include <poly/poly.h>
#include <poly/sign_condition.h>

#include "mcsat/utils/lp_data.h"
#include "mcsat/variable_db.h"

/**
 * A constraint of the form sgn(p(x)) = sgn_conition.
 */
typedef struct {
  /** The polynomial of the constraint */
  lp_polynomial_t* polynomial;

  /** The sign condition */
  lp_sign_condition_t sgn_condition;

  /** If this is a root constraint, this is the variable */
  lp_variable_t x;

  /** If this is a root constraint, this is the root index */
  size_t root_index;
} poly_constraint_t;

/**
 * Database of constraints
 */
typedef struct {
  /** The lp_data context */
  lp_data_t *lp_data;

  /** Vector of constraints */
  pvector_t constraints;

  /** Map from variables to constraint references */
  int_hmap_t var_to_constraint_map;

  /** List of all constraint variables */
  ivector_t all_constraint_variables;
} poly_constraint_db_t;

/** Construct the database */
void poly_constraint_db_construct(poly_constraint_db_t* db, lp_data_t* lp_data);

/** Construct the database */
poly_constraint_db_t* poly_constraint_db_new(lp_data_t* lp_data);

/** Destruct the database */
void poly_constraint_db_destruct(poly_constraint_db_t* db);

/** Delete the database */
void poly_constraint_db_delete(poly_constraint_db_t* db);

/** Get the sign condition of the constraint */
static inline
lp_sign_condition_t poly_constraint_get_sign_condition(const poly_constraint_t* cstr) {
  return cstr->sgn_condition;
}

/** Get the polynomial of the constraint */
static inline
const lp_polynomial_t* poly_constraint_get_polynomial(const poly_constraint_t* cstr) {
  return cstr->polynomial;
}

/** Is this a root constraint */
static inline
bool poly_constraint_is_root_constraint(const poly_constraint_t* cstr) {
  return cstr->x != lp_variable_null;
}

/** Get the variable of the root constraint */
static inline
lp_variable_t poly_constraint_get_variable(const poly_constraint_t* cstr) {
  return cstr->x;
}

/** Get the root index (if a root constraint) */
static inline
uint32_t poly_constraint_get_root_index(const poly_constraint_t* cstr) {
  return cstr->root_index;
}

/** Construct a regular constraint, takes over the polynomial */
void poly_constraint_construct_regular(poly_constraint_t* cstr, lp_polynomial_t* p, lp_sign_condition_t sgn_contition);

/** Construct a root constraint */
void poly_constraint_construct_root(poly_constraint_t* cstr, lp_polynomial_t* p, lp_sign_condition_t sgn_contition, lp_variable_t x, uint32_t root_index);

/** Allocate and construct the constraint, takes over the polynomial */
poly_constraint_t* poly_constraint_new_regular(lp_polynomial_t* p, lp_sign_condition_t sgn_contition);

/** Allocate and construct the constraint, takes over the polynomial */
poly_constraint_t* poly_constraint_new_root(lp_polynomial_t* p, lp_sign_condition_t sgn_contition, lp_variable_t x, uint32_t root_index);

/** Destruct the constraint */
void poly_constraint_destruct(poly_constraint_t* cstr);

/** Destruct and free the constraint */
void poly_constraint_delete(poly_constraint_t* cstr);

/** Adds one constraint to the constraint db. */
void poly_constraint_db_add_constraint(poly_constraint_db_t* db, variable_t constraint_var, poly_constraint_t* constraint);

/** Print the constraint */
void poly_constraint_print(const poly_constraint_t* cstr, FILE* out);

/** Print the constraint to mathematica */
void poly_constraint_print_mathematica(const poly_constraint_t* cstr, bool neageted, FILE* out);

/** Is this a valid constraint in the current order. */
bool poly_constraint_is_valid(const poly_constraint_t* cstr);

/** Check if the constraint is unit */
bool poly_constraint_is_unit(const poly_constraint_t* cstr, const lp_assignment_t* M);

/** Get the top variable of the constraint */
lp_variable_t poly_constraint_get_top_variable(const poly_constraint_t* cstr);

/** Get all constraints (as variables) */
static inline
const ivector_t* poly_constraint_db_get_constraints(const poly_constraint_db_t* db) {
  return &db->all_constraint_variables;
}

/** Returns true when the constraint_var has an associated polynomial in the db */
bool poly_constraint_db_has(poly_constraint_db_t* db, variable_t constraint_var);

/** Get the constraint of the variable (must exist) */
const poly_constraint_t* poly_constraint_db_get(poly_constraint_db_t* db, variable_t constraint_var);

/**
 * Evaluate the constraint. Returns the value, and sets the level to the level of the constraint.
 * recomputed. The return value is true if evaluation is OK. If return value is false,
 * it means that the top variable of a root constraint is not top anymore, so we
 * can ignore it.
 */
bool poly_constraint_evaluate(const poly_constraint_t* cstr, lp_data_t *lp_data, bool* value_out);

/** Get the feasible set of the constraint */
lp_feasibility_set_t* poly_constraint_get_feasible_set(const poly_constraint_t* cstr, const lp_assignment_t* m, bool negated);

/** Infer the bounds for this constraint (inferred_vars are lp_variables). Returns true if conflict detected. */
bool poly_constraint_infer_bounds(const poly_constraint_t* cstr, bool negated, lp_interval_assignment_t* m, ivector_t* inferred_vars);

/** Remove unused constraints */
void poly_constraint_db_gc_sweep(poly_constraint_db_t* db, plugin_context_t* ctx, const gc_info_t* gc_vars);

#endif /* LP_CONSTRAINT_DB_H */
