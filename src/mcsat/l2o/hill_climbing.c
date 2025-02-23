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

#include <math.h>

#include "mcsat/l2o/l2o.h"
#include "mcsat/l2o/l2o_internal.h"

#define IMPROVEMENT_THRESHOLD 0.0

typedef struct {
  uint32_t pos;
  uint32_t count;
  int_queue_t prio, prio_next;
  int_hset_t skip;
} var_order_t;

static
void init_var_order(var_order_t *o, uint32_t count) {
  assert(count > 0);
  init_int_queue(&o->prio, 0);
  init_int_queue(&o->prio_next, 0);
  init_int_hset(&o->skip, 0);
  o->pos = count - 1;
  o->count = count;
}

static inline
void delete_var_order(var_order_t *o) {
  delete_int_queue(&o->prio);
  delete_int_queue(&o->prio_next);
  delete_int_hset(&o->skip);
}

static inline
void var_prio(var_order_t *o, uint32_t x) {
  if (int_hset_add(&o->skip, x)) {
    int_queue_push(&o->prio_next, x);
  }
}

static
uint32_t next_var(var_order_t *o) {
  assert(o->pos < o->count);

  if (!int_queue_is_empty(&o->prio)) {
    assert(o->pos == 0);
    return int_queue_pop(&o->prio);
  }

  while (true) {
    o->pos++;
    if (o->pos == o->count) {
      int_queue_swap(&o->prio, &o->prio_next);
      assert(int_queue_is_empty(&o->prio_next));
      int_hset_reset(&o->skip);
      o->pos = 0;
      break;
    }
    assert(o->pos < o->count);
    if (!int_hset_member(&o->skip, o->pos)) {
      break;
    }
  }
  return o->pos;
}

static inline
bool did_improve(double *best, double new) {
  if (*best - new > IMPROVEMENT_THRESHOLD) {
    *best = new;
    return true;
  } else {
    return false;
  }
}

static inline
void update_cache(l2o_t *l2o) {
  double_hmap_swap(&l2o->eval_cache, &l2o->eval_map);
}

static
bool optimize_bool(l2o_t *l2o, term_t t, l2o_search_state_t *state, uint32_t v, double *best, uint32_t *eval_runs) {
  const double old_val = state->val[v];

  assert(is_boolean_term(l2o->terms, state->var[v]));
  assert(old_val == 0.0 || old_val == 1.0);

  // try opposite value
  state->val[v] = old_val == 0.0 ? 1.0 : 0.0;   // try opposite value
  double new_cost = l2o_evaluate_term_approx(l2o, t, state);
  (*eval_runs) ++;

  bool success = did_improve(best, new_cost);
  if (success) {
    update_cache(l2o);
  } else {
    // restore old value
    state->val[v] = old_val;
  }
  assert(success || state->val[v] == old_val);
  return success;
}

#define ACCELERATION (1.2)
#define CANDIDATES 4

static
bool optimize_number(l2o_t *l2o, term_t t, l2o_search_state_t *state, uint32_t v, double *step_size, double *best, uint32_t *eval_runs) {
  term_t term = state->var[v];
  double *const val = &state->val[v];
  const double old_val = state->val[v];
  const double old_step = *step_size;

  assert(is_integer_term(l2o->terms, term) || is_real_term(l2o->terms, term));

  const double candidate[CANDIDATES] = {
      -ACCELERATION,
      -1 / ACCELERATION,
      1 / ACCELERATION,
      ACCELERATION,
  };

  bool success = false;
  double best_val = old_val;
  double best_step = *step_size;

  for (int i = 0; i < CANDIDATES; ++i) {
    double step = old_step * candidate[i];
    *val = old_val + step;

    // If integer type, round to int
    if (is_integer_term(l2o->terms, term)) {
      *val = round(*val);
    }

    if (*val == old_val) {
      continue;
    }

    double new_cost = l2o_evaluate_term_approx(l2o, t, state);
    (*eval_runs) ++;

    if (did_improve(best, new_cost)) {
      update_cache(l2o);
      success = true;
      best_step = step;
      best_val = *val;
    }
  }

  *val = success ? best_val : old_val;
  *step_size = success ? best_step : old_step / ACCELERATION;
  return success;
}


#define MAX_ITER  1000
#define MAX_CALLS (MAX_ITER * 4)

void hill_climbing(l2o_t *l2o, term_t t, l2o_search_state_t *state) {
  assert(state->n_var >= 1);
  assert(state->n_var_fixed <= state->n_var);

  if (state->n_var_fixed == state->n_var) {
    return;
  }

  const term_table_t *terms = l2o->terms;
  const uint32_t n_var = state->n_var;
  const uint32_t n_var_flex = state->n_var - state->n_var_fixed;
  const term_t *const var = state->var;

  uint32_t n_iter = 0;         // number of iteration
  uint32_t n_calls = 0;        // Counter for calls to evaluator
  uint32_t n_var_visited = 0;  // Number of variables visited in an iteration

  var_order_t order;
  init_var_order(&order, n_var_flex);

  double step_size[n_var];
  for (uint32_t i = 0; i < n_var; ++i) {
    step_size[i] = 1.0;
  }

  // Reset evaluator cache cost (this forces the update of the cache at the next call)
  double best_cost = l2o_evaluate_term_approx(l2o, t, state);
  assert(double_hmap_find(&l2o->eval_map, t) != NULL);
  // force cache update
  update_cache(l2o);

  uint32_t var_idx = state->n_var_fixed + next_var(&order);

  // main loop
  while (best_cost > 0.0
         && n_var_visited <= n_var_flex
         && n_iter < MAX_ITER
         && n_calls < MAX_CALLS
  ) {
    assert(var_idx >= state->n_var_fixed);
    n_iter++;

    bool has_improved;
    if (is_boolean_term(terms, var[var_idx])) {
      has_improved = optimize_bool(l2o, t, state, var_idx, &best_cost, &n_calls);
    } else {
      has_improved = optimize_number(l2o, t, state, var_idx, &step_size[var_idx], &best_cost, &n_calls);
    }

    if (!has_improved) {    // Go to next var
      var_idx = state->n_var_fixed + next_var(&order);
      n_var_visited ++;
    } else {
      var_prio(&order, var_idx - state->n_var_fixed);
      n_var_visited = 0;
    }
  }

#ifndef NDEBUG
  for (int j = 0; j < state->n_var_fixed; ++j) {
    assert(step_size[j] == 1.0);
  }
#endif

  delete_var_order(&order);
}
