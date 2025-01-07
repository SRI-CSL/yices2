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

#include "model/models.h"
#include "context/context_types.h"

#include "mcsat/tracing.h"
#include "mcsat/l2o/l2o.h"
#include "mcsat/l2o/eval_vectors.h"
#include "mcsat/l2o/eval_hash_map.h"

#define IMPROVEMENT_THRESHOLD 0.0

/**
 * Performs hill climbing to minimize term t with variables v (where v_fixed are fixed variables) and starting value x.
 * Array of booleans v_fixed such that, if v_fixed[i] == true, then the value of v[i] must not be changed.
 * Array of doubles x are the current best and is updated to the new best.
 */
void hill_climbing(l2o_t *l2o, term_t t, uint32_t n_var, const term_t *v, const bool *v_fixed, double *x) {
  assert(n_var >= 1);

  uint32_t i = 0;
  const term_table_t *terms = l2o->terms;
  double acceptance_threshold = 0;
  //bool stop = false;
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
  evaluator_forget_cache_cost(&l2o->evaluator);
  double best_cost = l2o_evaluate_term_approx(l2o, t, n_var, v, x);

  if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
    printf("\n\n start_cost: %.50f", best_cost);
  }

  // List of variables indices
  // TODO use priority heap for indexes (or push to front)
  int_queue_t v_q;
  init_int_queue(&v_q, 0);

  for (i = 0; i < n_var; ++i) {
    // Initialize v_q with all non-fixed variables
    if (!v_fixed[i]) {
      int_queue_push(&v_q, i);
    }
  }

  if (int_queue_is_empty(&v_q)) {
    if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
      printf("\n\n all variables are fixed");
    }
    delete_int_queue(&v_q);
    return;
  }

  double current_x[n_var];  // Current assignment to use in the main loop
  double step_size[n_var];  // Starting step sizes
  for (i = 0; i < n_var; ++i) {
    current_x[i] = x[i];
    step_size[i] = 1;
  }

  int32_t current_dir_index = int_queue_pop(&v_q);

  // main loop
  while (best_cost > acceptance_threshold
         && n_var_visited <= n_var
         && n_iter < max_iter
         && n_calls < max_calls
  ) {
    assert(current_dir_index >= 0);

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
      printf("\nvar: %d", v[current_dir_index]);
    }

    // Check if variable is Boolean
    if (is_boolean_term(terms, v[current_dir_index])) {
      assert(x[current_dir_index] == 0 || x[current_dir_index] == 1);
      if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
        printf("\n is bool");
      }
      current_x[current_dir_index] = x[current_dir_index] == 0 ? 1.0 : 0.0;  // try opposite polarity
      current_cost = l2o_evaluate_term_approx(l2o, t, n_var, v, current_x);
      n_calls++;
      if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
        printf("\n current_cost: %.20f", current_cost);
      }
      if (best_cost - current_cost > IMPROVEMENT_THRESHOLD) {
        has_improved = true;
        x[current_dir_index] = current_x[current_dir_index];
        best_cost = current_cost;
        //direction_var = current_dir_index;
        continue;
      } else {
        current_x[current_dir_index] = x[current_dir_index];  // restore previous value
      }
    } else {
      // Else variable is Arith
      double best_step = 0;
      double best_x_i = x[current_dir_index];
      assert(has_improved == false);
      for (int candidate_index = 0; candidate_index < 4; ++candidate_index) {
        // Try to increment x[current_dir_index] by step_size  
        double step = step_size[current_dir_index] * candidate[candidate_index];
        current_x[current_dir_index] = x[current_dir_index] + step;

        // If integer type, round to int
        if (is_integer_term(terms, v[current_dir_index])) {
          current_x[current_dir_index] = round(current_x[current_dir_index]);
        }

        // If current_x equal to 
        if (current_x[current_dir_index] == x[current_dir_index]) {
          continue;
        }

        if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
          printf("\n increase by %f", step);
          printf("\n current_x[%d] <- %d", current_dir_index, (int) current_x[current_dir_index]);
        }

        current_cost = l2o_evaluate_term_approx(l2o, t, n_var, v, current_x);
        n_calls++;
        if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
          printf("\n current_cost: %.20f", current_cost);
        }
        if (current_cost < best_cost - IMPROVEMENT_THRESHOLD) {
          has_improved = true;
          best_step = step;
          best_x_i = current_x[current_dir_index];
          best_cost = current_cost;
          //direction_var = current_dir_index;
        }
      }
      if (!has_improved) {
        current_x[current_dir_index] = x[current_dir_index];  // restore previous value
        step_size[current_dir_index] = step_size[current_dir_index] / acceleration;     // decelerate
      } else {
        if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
          printf("\n best_step: %.20f", best_step);
        }
        current_x[current_dir_index] = best_x_i;   // keep best x found
        x[current_dir_index] = current_x[current_dir_index];   // update x
        step_size[current_dir_index] = best_step;   // keep successful acceleration   
      }
    }
    if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
      printf("\n\n has_improved: %d", has_improved);
    }
    if (!has_improved) {    // Go to next var
      int_queue_push(&v_q, current_dir_index);
      current_dir_index = int_queue_pop(&v_q);
      n_var_visited += 1;
    } else {
      n_var_visited = 0;
    }
  }

  if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
    printf("\n\n final_cost: %.50f", best_cost);
  }

  delete_int_queue(&v_q);
}
