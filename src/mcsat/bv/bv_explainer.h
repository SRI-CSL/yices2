/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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

#include "mcsat/mcsat_types.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/statistics.h"
#include "mcsat/plugin.h"

#include "bv_evaluator.h"

#include "utils/int_vectors.h"
#include "utils/ptr_vectors.h"
#include "utils/int_hash_sets.h"
#include "terms/term_manager.h"

typedef struct bv_subexplainer_s bv_subexplainer_t;

struct bv_subexplainer_s {

  /** MCSAT bit-vector plugin context */
  plugin_context_t* ctx;

  /** Watchlist manager for bit-vectors */
  watch_list_manager_t* wlm;

  /** The evaluator to use */
  bv_evaluator_t* eval;

  /** Name */
  const char* name;

  /** How many times has it been used */
  statistic_int_t* stat_explain_conflict_calls;

  /** How many times has it been used */
  statistic_int_t* stat_explain_propagation_calls;

  /** Destruct the explainer */
  void (*destruct) (bv_subexplainer_t* this);

  /** Returns true if the explainer can explain the given conflict. */
  bool (*can_explain_conflict) (bv_subexplainer_t* this, const ivector_t* conflict, variable_t conflict_var);

  /**
   * Returns the conflict as explained by the given sub-theory.
   * @param conflict_in input conflict (mcsat variables)
   * @param conflict_var the top variable of the conflict
   * @param conflict_out output explanation (terms)
   */
  void (*explain_conflict) (bv_subexplainer_t* this, const ivector_t* conflict_in, variable_t conflict_var, ivector_t* conflict_out);

  /** Returns true if the explainer can explain the given propagation. */
  bool (*can_explain_propagation) (bv_subexplainer_t* this, const ivector_t* reasons, variable_t x);

  /** Returns true if the explainer can explain the given propagation. */
  term_t (*explain_propagation) (bv_subexplainer_t* this, const ivector_t* reasons_in, variable_t x, ivector_t* reasons_out);
};

/** Base constructor for the plugin */
void bv_subexplainer_construct(bv_subexplainer_t* exp, const char* name, plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval);

typedef struct {

  /** Context */
  plugin_context_t* ctx;
  /** Term manager */
  term_manager_t* tm;
  /** Watch list manager */
  watch_list_manager_t* wlm;
  /** Bitvector evaluator */
  bv_evaluator_t* eval;

  /** Temp vector for conflict normalization */
  ivector_t tmp_conflict_vec;

  /** Vector of yices variables to use for mcsat variables */
  ivector_t variables;

  /** List of sub-explainers, to use in order */
  pvector_t subexplainers;

} bv_explainer_t;

/** Construct the explainer */
void bv_explainer_construct(bv_explainer_t* exp, plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval);

/** Destruct the explainer */
void bv_explainer_destruct(bv_explainer_t* exp);

/**
 * Returns the conflict as explained by the given sub-theory.
 * @param conflict_in input conflict (mcsat variables)
 * @param conflict_var the top variable of the conflict
 * @param conflict_out output explanation (terms)
 */
void bv_explainer_get_conflict(bv_explainer_t* exp, const ivector_t* conflict_in, variable_t conflict_var, ivector_t* conflict_out);

/**
 * Returns an explanation of the propagation of variable x -> v in the trail
 * The return is a term t such that
 * - reasons => x = t is valid,
 * - terms in reasons can all evaluate to true, and
 * - t can evaluate to v
 *
 * The vector reasons_in is the vector of variables that, when asserted,
 * imply the value v for x. A valid explanation would therefore be just
 * terms(reasons_i) for reasons_out, and term(v) for return. A more
 * reasonable explanation is usually needed for large domain variables.
 */
term_t bv_explainer_explain_propagation(bv_explainer_t* exp, variable_t x, const ivector_t* reasons_in, ivector_t* reasons_out);
