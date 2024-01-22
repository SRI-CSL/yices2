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

#ifndef FF_FEASIBLE_SET_DB_H
#define FF_FEASIBLE_SET_DB_H

#include <poly/poly.h>
#include <poly/integer.h>

#include "mcsat/variable_db.h"
#include "mcsat/mcsat_types.h"

/** Contains the map from variables to feasible sets that can be backtracked */
typedef struct ff_feasible_set_db_struct ff_feasible_set_db_t;

/** Create a new database */
ff_feasible_set_db_t* ff_feasible_set_db_new(plugin_context_t* ctx, lp_int_ring_t *K);

/** Delete the database */
void ff_feasible_set_db_delete(ff_feasible_set_db_t* db);

/**
 * Update the feasible set of the variable with a new set.
 * new_set must be a set (i.e. free of duplicates)
 *
 * If more than one reason, it's considered a disjunctive top-level assertion (clause);
 */
bool ff_feasible_set_db_update(ff_feasible_set_db_t* db, variable_t x, lp_value_t* new_set, size_t new_set_size, bool inverted, variable_t* reasons, size_t reasons_count);

/** Push the context */
void ff_feasible_set_db_push(ff_feasible_set_db_t* db);

/** Pop the context */
void ff_feasible_set_db_pop(ff_feasible_set_db_t* db);

/** Print the feasible set database */
void ff_feasible_set_db_print(ff_feasible_set_db_t* db, FILE* out);

/** Print the feasible sets of given variable */
void ff_feasible_set_db_print_var(ff_feasible_set_db_t* db, variable_t var, FILE* out);

/** Return any fixed variables */
variable_t ff_feasible_set_db_get_fixed(ff_feasible_set_db_t* db);

/** Marks all the top level reasons */
void ff_feasible_set_db_gc_mark(ff_feasible_set_db_t* db, gc_info_t* gc_vars);

#endif /* FF_FEASIBLE_SET_DB_H */
