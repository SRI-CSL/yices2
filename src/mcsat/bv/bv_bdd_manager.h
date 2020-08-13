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

#include "terms/terms.h"
#include "terms/bv_constants.h"
#include "mcsat/mcsat_types.h"

// TODO:
// 1. Memory for caching the BDDs, this can be reused per term, no need to be stingy
// 2.

/**
 * Structure responsible for all BDD interactions.
 *
 * Intended use:
 * - create the manager;
 * - register all bit-vector variables with the manager;
 * - create bdd's for terms that are unit over added variables
 * - compute with bdd's (e.g., and)
 * - pick bit-vector value from a BDD
 */
typedef struct bv_bdd_manager_s bv_bdd_manager_t;

/** Wrapper for the Cudd BDDs */
typedef struct {
  void* bdd[1];
} bdd_t;

/** Null BDD for convenience (bv_bdd_null.bdd == NULL) */
extern const bdd_t bdd_null;

/** Swap the two BDDs */
static inline
void bdd_swap(bdd_t* x, bdd_t* y) { void* tmp = x->bdd[0]; x->bdd[0] = y->bdd[0]; y->bdd[0] = tmp; }

/** Check if the two BDDs represent the same function */
static inline
bool bdd_eq(bdd_t x, bdd_t y) { return x.bdd[0] == y.bdd[0]; }

/** Wrapper for a sequence of Cudd's BDDs */
typedef struct {
  void** bdds;
} bv_bdd_t;

/** Null BDDs for convenience */
extern const bv_bdd_t bv_bdd_null;

/** Create a new BDD manager (allocate and construct) */
bv_bdd_manager_t* bv_bdd_manager_new(const plugin_context_t* ctx);

/** Delete the given BDD manager (destruct and deallocate) */
void bv_bdd_manager_delete(bv_bdd_manager_t* bddm);

/** Constant function true */
bdd_t bv_bdd_manager_true(const bv_bdd_manager_t* bddm);

/** Constant function false */
bdd_t bv_bdd_manager_false(const bv_bdd_manager_t* bddm);

/** Add term to the BDD manager (only added terms can be set to a value) */
void bv_bdd_manager_add_term(bv_bdd_manager_t* bddm, term_t t);

/** Check if BDD manager is aware of the term (has been added) */
bool bv_bdd_manager_has_term(const bv_bdd_manager_t* bddm, term_t term);

/** Set a value for a variable (copies the value) */
void bv_bdd_manager_set_bv_value(bv_bdd_manager_t* bddm, term_t x, const bvconstant_t* value);

/** Set a value for a 1-bit variable */
void bv_bdd_manager_set_bool_value(bv_bdd_manager_t* bddm, term_t t, bool value);

/**
 * Get a BDD representing a given Boolean literal. All variables except for
 * x will be replaced with their set values.
 *
 * @param t a term of the form t(x, y1, ..., yn), where all terms y_i have set values
 * @param t x a variable whose value will not be used
 * @return bdd a BDD representing values of individual bits of x [refcount attached]
 */
bdd_t bv_bdd_manager_get_bdd(bv_bdd_manager_t* bddm, term_t bv_literal, term_t x);

/**
 * Get a BDD vector representing a given bit-vector term. All variables except for x
 * will be replaced with their set values.
 *
 * @param t a term of the form t(x, y1, ..., yn), where all terms y_i have set values
 * @param t x a variable whose value will not be used
 * @return bdd a BDD representing values of individual bits of x [refcount attached]
 */
bv_bdd_t bv_bdd_manager_get_bv_bdd(bv_bdd_manager_t* bddm, term_t bv_term, term_t x);

/** Pick a value for a given variable that satisfies the given BDD(x). */
void bv_bdd_manager_pick_value(bv_bdd_manager_t* bddm, term_t x, bdd_t bdd, bvconstant_t* out);

/** Check if a given value satisfies the given BDD(x) */
bool bv_bdd_manager_is_model(bv_bdd_manager_t* bddm, term_t x, bdd_t bdd, const bvconstant_t* x_value);

/** Detach a BDD */
void bv_bdd_manager_bdd_detach(bv_bdd_manager_t* bddm, bdd_t bdd);

/** Attach a BDD */
void bv_bdd_manager_bdd_attach(bv_bdd_manager_t* bddm, bdd_t bdd);

/** Print a BDD with bitsize variables to output */
void bv_bdd_manager_bdd_print(const bv_bdd_manager_t* bddm, bdd_t bdd, FILE* out);

/** Check whether the given BDD is an empty set */
bool bv_bdd_manager_bdd_is_empty(const bv_bdd_manager_t* bddm, bdd_t bdd);

/** Check whether the given BDD represents one solution. */
bool bv_bdd_manager_bdd_is_point(const bv_bdd_manager_t* bddm, bdd_t bdd, uint32_t bitsize);

/** Intersect the two BDDs (result attached) */
bdd_t bv_bdd_manager_bdd_intersect(bv_bdd_manager_t* bddm, bdd_t bdd1, bdd_t bdd2);

/** Mark all the terms in the term manager */
void bv_bdd_manager_mark_terms(bv_bdd_manager_t* bddm);
