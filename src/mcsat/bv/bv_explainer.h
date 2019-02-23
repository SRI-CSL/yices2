/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
  statistic_int_t* stat_explain_calls;

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


