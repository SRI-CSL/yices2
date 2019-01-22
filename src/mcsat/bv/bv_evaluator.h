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

#include "mcsat/trail.h"
#include "mcsat/variable_db.h"
#include "mcsat/value.h"

/**
 * Structure to evaluate bit-vector constraints based on the current trail.
 */
typedef struct bv_evaluator_t {

  /** The context for evaluation */
  const plugin_context_t* ctx;

  /** Cached values (pointers to bvconstant_t) */
  pvector_t value_cache;

  /** Map from terms to values (indices in the bvconst array) */
  int_hmap_t term_values;

  /** Map from atoms to vales */
  int_hmap_t atom_values;

  /** Map from terms/atoms to levels */
  int_hmap_t level_map;

} bv_evaluator_t;

/** Construct the evaluator for the given plugin context */
void bv_evaluator_construct(bv_evaluator_t* evaluator, const plugin_context_t* ctx);

/** Destruct the evaluator */
void bv_evaluator_destruct(bv_evaluator_t* evaluator);

/**
 * Evaluate a BV constraint (atom), return the value (true/false) and set
 * the cstr_eval_level to the lowest level where the constraint still
 * evaluates.
 */
const mcsat_value_t* bv_evaluator_evaluate_var(bv_evaluator_t* evaluator, variable_t cstr, uint32_t* cstr_eval_level);

/**
 * Evaluate a BV constraint (atom), return the value (true/false) and set
 * the cstr_eval_level to the lowest level where the constraint still
 * evaluates.
 */
const mcsat_value_t* bv_evaluator_evaluate_term(bv_evaluator_t* evaluator, term_t cstr, uint32_t* cstr_eval_level);
