/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef MCSAT_L2O_INTERNAL_H_
#define MCSAT_L2O_INTERNAL_H_

#include "mcsat/l2o/l2o.h"
#include "mcsat/utils/int_lset.h"

#include <stdint.h>

typedef struct l2o l2o_t;

typedef struct {
  uint32_t n_var;
  uint32_t n_var_fixed;
  term_t *var;
  double *val;
} l2o_search_state_t;

/**
 * Map from a (non-negative) term id to a double, backed by a flat array indexed
 * by the term id (term ids are dense small integers, so this avoids hashing).
 * Live keys are tracked in `marked` so a reset is O(number of live entries) --
 * the same sparse-array-map scheme as utils/tag_map and utils/mark_vectors.
 */
typedef struct {
  double *val;       // val[k] for term id k
  uint8_t *present;  // present[k] != 0 iff k holds a live value
  ivector_t marked;  // the live keys (present[k] != 0); its size is the entry count
  uint32_t size;     // number of slots allocated
} term_double_map_t;

typedef struct {
  term_double_map_t eval_map;
  term_double_map_t eval_cache;
  ivector_t modified_vars;

  /** the l2o the evaluator is associated to */
  l2o_t *l2o;
} l2o_evaluator_t;

typedef struct l2o_cost_fx {
  /** Function to approximate the cost of the function under state
   *  May update internal state and caches. */
  double (*eval)(struct l2o_cost_fx *fx, const l2o_search_state_t *state);

  /** Updates the cache with the last evaluation result. */
  void (*update_cache)(struct l2o_cost_fx *fx);

  /** Fills all free variables of fx in v. */
  void (*get_free_vars)(const struct l2o_cost_fx *fx, ivector_t *v);

  /** Deletes the cost function. */
  void (*destruct)(struct l2o_cost_fx *fx);

  /** the l2o the cost fx is associated to */
  l2o_t *l2o;

  /** the trail the cost function is evaluated with */
  const mcsat_trail_t *trail;

  l2o_evaluator_t evaluator;
} l2o_cost_fx_t;

void l2o_search_state_construct_empty(l2o_search_state_t *state);

void l2o_search_state_destruct(l2o_search_state_t *state);

void l2o_search_state_print(const l2o_search_state_t *state, term_table_t *terms, FILE *file);

static inline
bool l2o_search_state_is_empty(const l2o_search_state_t *state) {
  return state->n_var == 0;
}

/** checks if l2o term t has any of free variables of set_of_vars */
bool l2o_term_has_variables(l2o_t *l2o, term_t t, const ivector_t *set_of_vars);

/**
 * Approximately evaluates term_eval t substituting variables v with double values x. The assignment has to be total.
 */
double l2o_evaluator_run_term(l2o_evaluator_t *evaluator, term_t term);

/** Returns a value that exists. */
double l2o_evaluator_get_value(const l2o_evaluator_t *evaluator, term_t term);

/** Returns a value if it is evaluated. Does not run the evaluator. */
double l2o_evaluator_get_value_if_exists(const l2o_evaluator_t *evaluator, term_t term);

void l2o_evaluator_construct(l2o_t *l2o, l2o_evaluator_t *evaluator);

void l2o_evaluator_destruct(l2o_evaluator_t *evaluator);

void l2o_evaluator_reset(l2o_evaluator_t *evaluator);

/** Moves the eval_map to cache.
 * The evaluator must not be used anymore until a new state is set or a reset is performed */
void l2o_evaluator_update_cache(l2o_evaluator_t *evaluator);

void l2o_evaluator_set_state(l2o_evaluator_t *evaluator, const l2o_search_state_t *state);

/**
 * Hill climbing algorithm with cost function t (to be minimized), variables v (some of which have fixed values), and starting point x
 */
void hill_climbing(l2o_t *l2o, l2o_cost_fx_t *fx, l2o_search_state_t *state);


typedef struct {
  l2o_cost_fx_t fx;

  /** The term to evaluate. */
  ivector_t terms;
} l2o_cost_fx_term_t;

void l2o_cost_fx_term_construct(l2o_t *l2o, l2o_cost_fx_term_t *fx);

void l2o_cost_fx_term_add(l2o_cost_fx_term_t *fx, term_t t);

bool l2o_is_valid_term(l2o_t *l2o, term_t t);

double l2o_calculate(l2o_t *l2o, term_t t, l2o_evaluator_t *eval);

#endif /* MCSAT_L2O_INTERNAL_H_ */
