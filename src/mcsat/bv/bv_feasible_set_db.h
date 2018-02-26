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
 
#ifndef BV_FEASIBLE_SET_DB_H_
#define BV_FEASIBLE_SET_DB_H_


#include <stdio.h>
#include <cudd.h>

#include "mcsat/variable_db.h"
#include "mcsat/mcsat_types.h"

/** Contains the map from variables to feasible sets that can be backtracked */
typedef struct bv_feasible_set_db_struct bv_feasible_set_db_t;

/** Get the BDD manager */
DdManager* bv_feasible_manager(bv_feasible_set_db_t* db);

/** Create a new database */
bv_feasible_set_db_t* bv_feasible_set_db_new(term_table_t* terms, variable_db_t* var_db, const mcsat_trail_t* trail);

/** Delete the database */
void bv_feasible_set_db_delete(bv_feasible_set_db_t* db);

/* Enter a new variable in the database, with domain 1 */
void bv_feasible_set_db_set_init(bv_feasible_set_db_t* db, variable_t x, uint32_t bitsize);

/** Mark that x should be different from given value. */
bool bv_feasible_set_db_set_update(bv_feasible_set_db_t* db, variable_t x, term_t reason, bvconstant_t* v);

/* /\** Get a feasible value. *\/ */
/* uint32_t bv_feasible_set_db_get(bv_feasible_set_db_t* db, variable_t x); */

/* /\** Push the context *\/ */
/* void bv_feasible_set_db_push(bv_feasible_set_db_t* db); */

/* /\** Pop the context *\/ */
/* void bv_feasible_set_db_pop(bv_feasible_set_db_t* db); */

/* /\** Get the reason for a conflict on x. Outputs conjunction of terms to the vector. *\/ */
/* void bv_feasible_set_db_get_conflict(bv_feasible_set_db_t* db, variable_t x, ivector_t* conflict); */

/* /\** Get the reason for a propagation on x. *\/ */
/* variable_t bv_feasible_set_db_get_eq_reason(bv_feasible_set_db_t* db, variable_t x); */

/* /\** Return any fixed variables *\/ */
/* variable_t bv_feasible_set_db_get_fixed(bv_feasible_set_db_t* db); */

/* /\** Print the feasible set database *\/ */
/* void bv_feasible_set_db_print(bv_feasible_set_db_t* db, FILE* out); */

/* /\** Print the feasible sets of given variable *\/ */
/* void bv_feasible_set_db_print_var(bv_feasible_set_db_t* db, variable_t var, FILE* out); */

/* /\** Marks all the top level reasons *\/ */
/* void bv_feasible_set_db_gc_mark(bv_feasible_set_db_t* db, gc_info_t* gc_vars); */

/* /\** Marks all the top level reasons *\/ */
/* void bv_feasible_set_db_gc_sweep(bv_feasible_set_db_t* db, const gc_info_t* gc_vars); */

#endif /* BV_FEASIBLE_SET_DB_H_ */
