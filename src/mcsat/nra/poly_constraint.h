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
 
#pragma once

#include <stdio.h>
#include <poly/polynomial.h>
#include <poly/sign_condition.h>

#include "mcsat/nra/nra_plugin_internal.h"
#include "utils/int_hash_map.h"

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

/** Print the constraint */
void poly_constraint_print(const poly_constraint_t* cstr, FILE* out);

/** Print the constraint to mathematica */
void poly_constraint_print_mathematica(const poly_constraint_t* cstr, bool neageted, FILE* out);

/** Get the feasible set of the constraint */
lp_feasibility_set_t* poly_constraint_get_feasible_set(const poly_constraint_t* cstr, const lp_assignment_t* m, bool negated);

/** Infer the bounds for this constraint (inferred_vars are lp_variables). Returns true if conflict detected. */
bool poly_constraint_infer_bounds(const poly_constraint_t* cstr, bool negated, lp_interval_assignment_t* m, ivector_t* inferred_vars);

/**
 * Is this a valid constraint in the current order.
 */
bool poly_constraint_is_valid(const poly_constraint_t* cstr);

/**
 * Evaluate the constraint. Returns the value, and sets the level to the level of the constraint.
 * recomputed. The return value is true if evaluation is OK. If return value is false,
 * it means that the top variable of a root constraint is not top anymore, so we
 * can ignore it.
 */
bool poly_constraint_evaluate(const poly_constraint_t* cstr, nra_plugin_t* nra, bool* value_out);

/** Get the top variable of the constraint */
lp_variable_t poly_constraint_get_top_variable(const poly_constraint_t* cstr);

/** Get the sign condition of the constraint */
lp_sign_condition_t poly_constraint_get_sign_condition(const poly_constraint_t* cstr);

/** Get the polynomial of the constraint */
const lp_polynomial_t* poly_constraint_get_polynomial(const poly_constraint_t* cstr);

/** Is this a root constraint */
bool poly_constraint_is_root_constraint(const poly_constraint_t* cstr);

/** Get the variable of the root constraint */
lp_variable_t poly_constraint_get_variable(const poly_constraint_t* cstr);

/** Get the root index (if a root constraint) */
uint32_t poly_constraint_get_root_index(const poly_constraint_t* cstr);

/** Check if the constraint is unit */
bool poly_constraint_is_unit(const poly_constraint_t* cstr, const lp_assignment_t* M);

/** Try to resolve the two constraints with Fourier-Motzkin resolution */
bool poly_constraint_resolve_fm(const poly_constraint_t* c0, bool c0_negated, const poly_constraint_t* c1, bool c1_negated, nra_plugin_t* nra, ivector_t* out);

/** Construct the database */
void poly_constraint_db_construct(poly_constraint_db_t* db, nra_plugin_t* nra);

/** Construct the database */
poly_constraint_db_t* poly_constraint_db_new(nra_plugin_t* nra);

/** Destruct the database */
void poly_constraint_db_destruct(poly_constraint_db_t* db);

/** Delete the database */
void poly_constraint_db_delete(poly_constraint_db_t* db);

/** Get all constraints (as variables) */
const ivector_t* poly_constraint_db_get_constraints(const poly_constraint_db_t* db);

/** Get the constraint of the variable (must exist) */
const poly_constraint_t* poly_constraint_db_get(poly_constraint_db_t* db, variable_t constraint_var);

/** Compute an approximation of the constraint value with interval computation */
const mcsat_value_t* poly_constraint_db_approximate(poly_constraint_db_t* db, variable_t constraint_var, nra_plugin_t* nra);

/** Add a new constraint */
void poly_constraint_db_add(poly_constraint_db_t* db, variable_t constraint_var);

/** Remove unised constraints */
void poly_constraint_db_gc_sweep(poly_constraint_db_t* db, const gc_info_t* gc_vars);
