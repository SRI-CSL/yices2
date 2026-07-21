/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */
 
#pragma once

#include <poly/poly.h>
#include <stdio.h>

#include "mcsat/variable_db.h"
#include "mcsat/mcsat_types.h"
#include "mcsat/value.h"

typedef struct na_plugin_s na_plugin_t;

/** Contains the map from variables to feasible sets that can be backtracked */
typedef struct feasible_set_db_struct feasible_set_db_t;

/** Create a new database */
feasible_set_db_t* feasible_set_db_new(na_plugin_t * ctx);

/** Delete the database */
void feasible_set_db_delete(feasible_set_db_t* db);

/**
 * Update the feasible set of the variable with a new set. The new set is kept
 * if it reduces the existing feasible set. Returns true if consistent.
 *
 * If more than one reason, it's considered a disjunctive top-level assertion (clause);
 */
bool feasible_set_db_update(feasible_set_db_t* db, variable_t x, lp_feasibility_set_t* new_set, const variable_t* reasons, uint32_t reasons_count);

/** Get the feasible set of a variable */
lp_feasibility_set_t* feasible_set_db_get(feasible_set_db_t* db, variable_t x);

/** Push the context */
void feasible_set_db_push(feasible_set_db_t* db);

/** Pop the context */
void feasible_set_db_pop(feasible_set_db_t* db);

/** Get the reason for a conflict on x. Feasible set of x should be empty. */
void feasible_set_db_get_conflict_reasons(const feasible_set_db_t* db, variable_t x, const mcsat_value_t* x_value, ivector_t* reasons_out, ivector_t* lemma_reasons_out);

/** Return any fixed variables */
variable_t feasible_set_db_get_fixed(feasible_set_db_t* db);

/** Print the feasible set database */
void feasible_set_db_print(feasible_set_db_t* db, FILE* out);

/** Print the feasible sets of given variable */
void feasible_set_db_print_var(feasible_set_db_t* db, variable_t var, FILE* out);

/** Returns an unassigned variable with a value in its feasible set, or variable_null otherwise */
variable_t feasible_set_db_get_cheap_unassigned(feasible_set_db_t* db, lp_value_t* value);

/** Marks all the top level reasons */
void feasible_set_db_gc_mark(feasible_set_db_t* db, gc_info_t* gc_vars);

/** Get an interval approximation of the value */
void feasible_set_db_approximate_value(feasible_set_db_t* db, variable_t x, lp_interval_t* result);
