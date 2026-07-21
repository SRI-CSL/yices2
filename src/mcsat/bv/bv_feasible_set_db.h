/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#pragma once

#include <stdio.h>

#include "mcsat/variable_db.h"
#include "mcsat/mcsat_types.h"
#include "mcsat/value.h"
#include "mcsat/bv/bv_bdd_manager.h"

/** Contains the map from variables to feasible sets that can be backtracked */
typedef struct bv_feasible_set_db_s bv_feasible_set_db_t;

/** Create a new database */
bv_feasible_set_db_t* bv_feasible_set_db_new(plugin_context_t* ctx, bv_bdd_manager_t* bddm);

/** Delete the database */
void bv_feasible_set_db_delete(bv_feasible_set_db_t* db);

/**
 * Update the feasible set of the variable with a new set. The new set is kept
 * if it reduces the existing feasible set. Returns true if consistent.
 *
 * The new set is your responsibility to deref.
 *
 * If more than one reason, it's considered a disjunctive top-level assertion.
 */
bool bv_feasible_set_db_update(bv_feasible_set_db_t* db, variable_t x, bdd_t new_set, variable_t* reasons, uint32_t reasons_count);

/** Get the feasible set of a variable */
bdd_t bv_feasible_set_db_get(const bv_feasible_set_db_t* db, variable_t x);

/** Pick a value from the feasible set */
const mcsat_value_t* bv_feasible_set_db_pick_value(bv_feasible_set_db_t* db, variable_t x);

/** Push the context */
void bv_feasible_set_db_push(bv_feasible_set_db_t* db);

/** Pop the context */
void bv_feasible_set_db_pop(bv_feasible_set_db_t* db);

typedef enum {
  /** Get reasons for dom(x) = {} */
  EXPLAIN_EMPTY,
  /** Get reasons fro dom(x) = { v } */
  EXPLAIN_SINGLETON,
  /** Get reasons for v \not\in dom(x) */
  EXPLAIN_ASSUMPTION
} bv_feasible_explain_mode_t;

/** Get the reason for a conflict on x. Feasible set of x should be empty. */
void bv_feasible_set_db_get_reasons(const bv_feasible_set_db_t* db, variable_t x, ivector_t* reasons_out, ivector_t* lemma_reasons, bv_feasible_explain_mode_t mode);

/** Return any fixed variables */
variable_t bv_feasible_set_db_get_fixed(bv_feasible_set_db_t* db);

/** Print the feasible set database */
void bv_feasible_set_db_print(const bv_feasible_set_db_t* db, FILE* out);

/** Print the feasible sets of given variable */
void bv_feasible_set_db_print_var(const bv_feasible_set_db_t* db, variable_t var, FILE* out);

/** Marks all the top level reasons */
void bv_feasible_set_db_gc_mark(bv_feasible_set_db_t* db, gc_info_t* gc_vars);
