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
#include "mcsat/tracing.h"

#define IMPROVEMENT_THRESHOLD 0.0

typedef struct {
  uint32_t pos;
  uint32_t count;
  int_queue_t prio, prio_next;
  int_hset_t skip;
} var_order_t;

static
void init_var_order(var_order_t *o, uint32_t count) {
  init_int_queue(&o->prio, 0);
  init_int_queue(&o->prio_next, 0);
  init_int_hset(&o->skip, 0);
  o->pos = 0;
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
      int_hset_reset(&o->skip);
      o->pos = 0;
      break;
    }
    if (!int_hset_member(&o->skip, o->pos)) {
      break;
    }
  }
  return o->pos;
}

/**
 * Performs hill climbing to minimize term t with variables v (where v_fixed are fixed variables) and starting value x.
 * Array of booleans v_fixed such that, if v_fixed[i] == true, then the value of v[i] must not be changed.
 * Array of doubles x are the current best and is updated to the new best.
 */
void hill_climbing(l2o_t *l2o, term_t t, l2o_search_state_t *state) {
  assert(state->n_var >= 1);
  assert(state->n_var_fixed <= state->n_var);

  if (state->n_var_fixed == state->n_var) {
    if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
      printf("\n\n all variables are fixed");
    }
    return;
  }

  uint32_t i = 0;
  const term_table_t *terms = l2o->terms;
  double acceptance_threshold = 0;
  uint32_t n_iter = 0;
  uint32_t n_calls = 0; // Counter for calls to evaluator
  uint32_t max_iter = 1000;
  uint32_t max_calls = max_iter * 4;
  uint32_t n_var_visited = 0;  // Number of variables visited in an iteration

  double acceleration = 1.2;
  double candidate[4];
  candidate[0] = -acceleration;
  candidate[1] = -1 / acceleration;
  candidate[2] = 1 / acceleration;
  candidate[3] = acceleration;
  // TODO cast to int 

  // Reset evaluator cache cost (this forces the update of the cache at the next call)
  double best_cost = l2o_evaluate_term_approx(l2o, t, state, true);

  if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
    printf("\n\n start_cost: %.50f", best_cost);
  }

  uint32_t n_var = state->n_var;

  var_order_t order;
  init_var_order(&order, state->n_var - state->n_var_fixed);

  const term_t *var  = state->var;
  double *val_cur   = state->val;                               // the current value of the state
  double *val_old   = safe_malloc(sizeof(double) * n_var), // the old value of the state, used to reset if no progress was made
         *step_size = safe_malloc(sizeof(double) * n_var); // the step size

  for (i = 0; i < n_var; ++i) {
    val_old[i] = val_cur[i];
    step_size[i] = 1.0;
  }

  uint32_t current_dir_index = state->n_var_fixed + next_var(&order);

  // main loop
  while (best_cost > acceptance_threshold
         && n_var_visited <= n_var
         && n_iter < max_iter
         && n_calls < max_calls
  ) {
    assert(current_dir_index >= state->n_var_fixed);

    n_iter = n_iter + 1;
    if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
      printf("\n\n*n_iter: %d", n_iter);
      printf("\n*n_var_visited: %d", n_var_visited);
      printf("\n*n_var: %d", n_var);
      printf("\nbest_cost: %.20f", best_cost);
    }

    bool has_improved = false;
    double current_cost = best_cost;

    if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
      printf("\nvar: %d", var[current_dir_index]);
    }

    // Check if variable is Boolean
    if (is_boolean_term(terms, var[current_dir_index])) {
      assert(val_old[current_dir_index] == 0.0 || val_old[current_dir_index] == 1.0);
      if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
        printf("\n is bool");
      }
      val_cur[current_dir_index] = val_old[current_dir_index] == 0 ? 1.0 : 0.0;  // try opposite polarity
      current_cost = l2o_evaluate_term_approx(l2o, t, state, false);
      n_calls++;
      if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
        printf("\n current_cost: %.20f", current_cost);
      }
      if (best_cost - current_cost > IMPROVEMENT_THRESHOLD) {
        has_improved = true;
        val_old[current_dir_index] = val_cur[current_dir_index];
        best_cost = current_cost;
        //direction_var = current_dir_index;
        continue;
      } else {
        val_cur[current_dir_index] = val_old[current_dir_index];  // restore previous value
      }
    } else {
      // else variable is arith
      double best_step = 0;
      assert(has_improved == false);
      assert(val_old[current_dir_index] == val_cur[current_dir_index]);
      double best_x_i = val_old[current_dir_index];
      for (int candidate_index = 0; candidate_index < 4; ++candidate_index) {
        // Try to increment x[current_dir_index] by step_size  
        double step = step_size[current_dir_index] * candidate[candidate_index];
        val_cur[current_dir_index] = val_old[current_dir_index] + step;

        // If integer type, round to int
        if (is_integer_term(terms, var[current_dir_index])) {
          val_cur[current_dir_index] = round(val_cur[current_dir_index]);
        }

        if (val_cur[current_dir_index] == val_old[current_dir_index]) {
          continue;
        }

        if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
          printf("\n increase by %f", step);
          printf("\n current_x[%d] <- %f", current_dir_index, val_cur[current_dir_index]);
        }

        current_cost = l2o_evaluate_term_approx(l2o, t, state, false);
        n_calls++;
        if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
          printf("\n current_cost: %.20f", current_cost);
        }
        if (current_cost < best_cost - IMPROVEMENT_THRESHOLD) {
          has_improved = true;
          best_step = step;
          best_x_i = val_cur[current_dir_index];
          best_cost = current_cost;
          //direction_var = current_dir_index;
        }
      }
      if (!has_improved) {
        val_cur[current_dir_index] = val_old[current_dir_index];  // restore previous value
        step_size[current_dir_index] = step_size[current_dir_index] / acceleration;     // decelerate
      } else {
        if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
          printf("\n best_step: %.20f", best_step);
        }
        val_cur[current_dir_index] = best_x_i;   // keep best x found
        val_old[current_dir_index] = best_x_i;   // update x
        step_size[current_dir_index] = best_step;   // keep successful acceleration   
      }
    }
    if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
      printf("\n\n has_improved: %d", has_improved);
    }
    if (!has_improved) {    // Go to next var
      current_dir_index = state->n_var_fixed + next_var(&order);
      n_var_visited += 1;
    } else {
      var_prio(&order, current_dir_index);
      n_var_visited = 0;
    }
  }

  if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
    printf("\n\n final_cost: %.50f", best_cost);
  }

#ifndef NDEBUG
  for (uint32_t j = 0; j < n_var; ++j) {
    assert(val_cur[j] == val_old[j]);
  }
  for (int j = 0; j < state->n_var_fixed; ++j) {
    assert(step_size[j] == 1.0);
  }
#endif

  free(val_old);
  free(step_size);
  delete_var_order(&order);
}
