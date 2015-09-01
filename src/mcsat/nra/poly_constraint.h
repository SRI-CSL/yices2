/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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

/**
 * Evaluate the constraint. Returns the value, and sets the level to the level of the constraint.
 * If variables are given (variable_null_terminated), they are used to compute the level, otherwise (if 0) list of variables is
 * recomputed.
 */
const mcsat_value_t* poly_constraint_evaluate(const poly_constraint_t* cstr, const variable_t* var_list, nra_plugin_t* nra, uint32_t* cstr_level);

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

/** Construct the database */
void poly_constraint_db_construct(poly_constraint_db_t* db, nra_plugin_t* nra);

/** Construct the database */
poly_constraint_db_t* poly_constraint_db_new(nra_plugin_t* nra);

/** Destruct the database */
void poly_constraint_db_destruct(poly_constraint_db_t* db);

/** Delete the database */
void poly_constraint_db_delete(poly_constraint_db_t* db);

/** Get the constraint of the variable (must exist) */
const poly_constraint_t* poly_constraint_db_get(poly_constraint_db_t* db, variable_t constraint_var);

/** Add a new constraint */
void poly_constraint_db_add(poly_constraint_db_t* db, variable_t constraint_var);

/** Mark all the variables from the constraints */
void poly_constraint_db_gc_mark(poly_constraint_db_t* db, gc_info_t* gc_vars);

/** Remove unised constraints */
void poly_constraint_db_gc_sweep(poly_constraint_db_t* db, const gc_info_t* gc_vars);
