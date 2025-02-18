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

/** Get the varset_table index of the set of free variables in t */
int32_t get_freevars_index(const l2o_t* l2o, term_t t);

/** Get the set of free variables in t */
const int_hset_t* get_freevars(const l2o_t* l2o, term_t t);

/** Get the set of free variables from a term given its varset_table index  */
const int_hset_t* get_freevars_from_index(const l2o_t* l2o, int32_t index);

composite_term_t* get_composite(term_table_t* terms, term_kind_t kind, term_t t);

/**
 * Approximately evaluates term_eval t substituting variables v with double values x. The assignment has to be total.
 */
double l2o_evaluate_term_approx(l2o_t *l2o, term_t term, const l2o_search_state_t *state, bool force_cache_update);

/**
 * Hill climbing algorithm with cost function t (to be minimized), variables v (some of which have fixed values), and starting point x
 */
void hill_climbing(l2o_t *l2o, term_t t, l2o_search_state_t *state);

#endif /* MCSAT_L2O_INTERNAL_H_ */
