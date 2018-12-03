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

#include "utils/int_vectors.h"
#include "utils/int_hash_sets.h"
#include "terms/term_manager.h"

/** Different theories that we can explain */
typedef enum {
  /** Equality */
  BV_TH_EQ = 0,
  /** Equality, extraction, concatenation */
  BV_TH_EQ_EXT_CON,
  /** Bitwise operation (NOT, OR) */
  BV_TH_BITWISE,
  /** Shifting */
  BV_TH_SHIFT,
  /** Arithmetic comparison */
  BV_TH_ARITH_CMP,
  /** Arithmetic */
  BV_TH_ARITH,
  /** All together */
  BV_TH_FULL
} bv_subtheory_t;

#define BV_TH_COUNT (BV_TH_FULL + 1)

typedef struct {
  /** Context */
  const plugin_context_t* ctx;
  /** Term manager */
  term_manager_t* tm;
  /** Watch list manager */
  watch_list_manager_t* wlm;

  /** Cache when visiting terms */
  int_hset_t visited_cache;

  struct {
    statistic_int_t* th_eq;
    statistic_int_t* th_eq_ext_con;
    statistic_int_t* th_full;
  } stats;

} bv_explainer_t;

/** Construct the explainer */
void bv_explainer_construct(bv_explainer_t* exp, const plugin_context_t* ctx, watch_list_manager_t* wlm);

/** Destruct the explainer */
void bv_explainer_destruct(bv_explainer_t* exp);

/**
 * Returns the subtheory best suited to explain the conflict
 * @param conflict vector of mcsat variables
 * */
bv_subtheory_t bv_explainer_get_subtheory(bv_explainer_t* exp, const ivector_t* conflict);

/**
 * Returns the conflict as explained by the given sub-theory.
 * @param conflict_in input conflict (mcsat variables)
 * @param conflict_var the top variable of the conflict
 * @param conflict_out outut explanation (terms)
 */
void bv_explainer_get_conflict(bv_explainer_t* exp, const ivector_t* conflict_in, variable_t conflict_var, ivector_t* conflict_out);
