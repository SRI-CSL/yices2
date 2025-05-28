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

#ifndef MCSAT_L2O_INTERNAL_H_
#define MCSAT_L2O_INTERNAL_H_

#include "mcsat/l2o/l2o.h"
#include "mcsat/utils/int_lset.h"

#include <stdint.h>

typedef struct {
  uint32_t n_var;
  uint32_t n_var_fixed;
  term_t *var;
  double *val;
} l2o_search_state_t;


void l2o_search_state_construct_empty(l2o_search_state_t *state);

void l2o_search_state_destruct(l2o_search_state_t *state);

static inline
bool l2o_search_state_is_empty(const l2o_search_state_t *state) {
  return state->n_var == 0;
}

/** checks if l2o term t has any of free variables of set_of_vars */
bool l2o_term_has_variables(l2o_t *l2o, term_t t, const ivector_t *set_of_vars);

/**
 * Approximately evaluates term_eval t substituting variables v with double values x. The assignment has to be total.
 */
double l2o_evaluate_term_approx(l2o_t *l2o, term_t term, const l2o_search_state_t *state);

/**
 * Hill climbing algorithm with cost function t (to be minimized), variables v (some of which have fixed values), and starting point x
 */
void hill_climbing(l2o_t *l2o, term_t t, l2o_search_state_t *state);


typedef struct {
  /** zero-terminated list of clauses with its terms */
  term_t *lit;

  /** capacity of lit */
  uint32_t capacity;

  /** offsets in lit with start of a new clause */
  ivector_t clause_ids;

  /** map of var -> [clause_id] */
  int_lset_t var2clause;

  /** the bool plugin to query */
  l2o_t *l2o;
} l2o_cost_fx_t;

void l2o_cost_fx_construct(l2o_t *l2o, l2o_cost_fx_t *fx);

void l2o_cost_fx_destruct(l2o_cost_fx_t *fx);

/** counts the number of unsatisfied clauses in the given state. */
uint32_t l2o_cost_fx_eval(const l2o_cost_fx_t *fx, const l2o_search_state_t *state);

/** adds an assertion to the cost function. Returns the number of added clauses. */
uint32_t l2o_cost_fx_add(l2o_cost_fx_t *fx, variable_t v);

void l2o_cost_fx_print(const l2o_cost_fx_t *fx, FILE *out);

#endif /* MCSAT_L2O_INTERNAL_H_ */
