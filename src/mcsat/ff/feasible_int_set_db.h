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

#ifndef FEASIBLE_INT_SET_DB_H
#define FEASIBLE_INT_SET_DB_H

#include <poly/poly.h>
#include <poly/integer.h>

#include "mcsat/variable_db.h"
#include "mcsat/mcsat_types.h"

/** Contains the map from variables to feasible sets that can be backtracked */
typedef struct feasible_int_set_db_struct feasible_int_set_db_t;

/** Create a new database */
feasible_int_set_db_t* feasible_int_set_db_new(plugin_context_t* ctx, const lp_int_ring_t *K);

/** Delete the database */
void feasible_int_set_db_delete(feasible_int_set_db_t* db);

/**
 * Update the feasible set of the variable with a new set.
 * new_set must be a set (i.e. free of duplicates)
 *
 * If more than one reason, it's considered a disjunctive top-level assertion (clause);
 */
bool feasible_int_set_db_update(feasible_int_set_db_t* db, variable_t x, lp_value_t* new_set, size_t new_set_size, bool inverted, variable_t* reasons, size_t reasons_count);

/** Push the context */
void feasible_int_set_db_push(feasible_int_set_db_t* db);

/** Pop the context */
void feasible_int_set_db_pop(feasible_int_set_db_t* db);

/** Print the feasible set database */
void feasible_int_set_db_print(feasible_int_set_db_t* db, FILE* out);

/** Print the feasible sets of given variable */
void feasible_int_set_db_print_var(feasible_int_set_db_t* db, variable_t var, FILE* out);

/** Return any fixed variables */
variable_t feasible_int_set_db_get_fixed(feasible_int_set_db_t* db);

/** Marks all the top level reasons */
void feasible_int_set_db_gc_mark(feasible_int_set_db_t* db, gc_info_t* gc_vars);

#endif /* FEASIBLE_INT_SET_DB_H */
