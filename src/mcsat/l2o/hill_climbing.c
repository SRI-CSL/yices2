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

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "mcsat/tracing.h"

#include "terms/term_explorer.h"
#include "terms/free_var_collector.h"

#include "model/models.h"

#include "context/context_types.h"

#include "yices.h"
#include "api/yices_api_lock_free.h"
#include "api/yices_extensions.h"
#include "api/yices_globals.h"

#include "mcsat/l2o/l2o.h"
#include "mcsat/l2o/eval_vectors.h"
#include "mcsat/l2o/eval_hash_map.h"

#include "mcsat/l2o/dl_int_lists.h"

#define IMPROVEMENT_THRESHOLD 0

/*
Gets as input:
- Term t representing a cost function to be minimized
- Number of variables n_var
- Array of variables v
- Array of doubles x 
- Array of booleans v_fixed such that, if v_fixed[i] == true, then the value of v[i] must not be changed
*/

double *hill_climbing(l2o_t *l2o, term_t t, uint32_t n_var, term_t *v, double *x, const bool *v_fixed) {
  assert(n_var >= 1);

  uint32_t i = 0;
  term_table_t *terms = l2o->terms;
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

  //uint32_t direction_var = 0; // index of a variable whose change improved the cost
  // IMPROV: use list

  // Reset evaluator cache cost (this forces the update of the cache at the next call)
  evaluator_forget_cache_cost(&l2o->evaluator);
  double best_cost = l2o_evaluate_term_approx(l2o, n_var, v, x, t);
  double *best_x = (double *) safe_malloc(n_var * sizeof(double));

  if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
    printf("\n\n start_cost: %.50f", best_cost);
  }

  // List of variables indices, ordered by success recency
  // TODO why using a linked list in the first place
  static dl_int_list_t var_list;  // TODO this should not be static
  clear_list(&var_list);

  // Elements of var_list
  dl_int_list_t v_elems[n_var];

  for (i = 0; i < n_var; ++i) {
    // Copy x into best_x
    best_x[i] = x[i];

    // Initialize var_list elements for non-fixed variables
    if (!v_fixed[i]) {
      v_elems[i].elem = i;
      list_insert_pre(&var_list, &v_elems[i]);  // TODO it counts the first element two times
    }
  }


  double current_x[n_var];  // Current assignment to use in the main loop
  double step_size[n_var];  // Starting step sizes
  for (i = 0; i < n_var; ++i) {
    current_x[i] = best_x[i];
    step_size[i] = 1;
  }


  // Current direction (as list element)
  dl_int_list_t *current_dir = &var_list;

  // Current direction (as variable index) 
  uint32_t current_dir_index = current_dir->elem;

  // Enter main loop
  while (!(best_cost <= acceptance_threshold) && (n_var_visited <= n_var) && (n_iter < max_iter) &&
         (n_calls < max_calls)) {
    n_iter = n_iter + 1;
    if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
      printf("\n\n*n_iter: %d", n_iter);
      printf("\n*n_var_visited: %d", n_var_visited);
      printf("\n*n_var: %d", n_var);
    }
    bool has_improved = false;
    if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
      printf("\nbest_cost: %.20f", best_cost);
    }
    double current_cost = best_cost;

    if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
      printf("\nvar: %d", v[current_dir_index]);
    }

    // Check if variable is Boolean
    if (is_boolean_term(terms, v[current_dir_index])) {
      if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
        printf("\n is bool");
      }
      current_x[current_dir_index] = !best_x[current_dir_index];  // try opposite polarity        
      current_cost = l2o_evaluate_term_approx(l2o, n_var, v, current_x, t);
      n_calls++;
      if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
        printf("\n current_cost: %.20f", current_cost);
      }
      if (best_cost - current_cost > IMPROVEMENT_THRESHOLD) {
        has_improved = true;
        best_x[current_dir_index] = current_x[current_dir_index];
        best_cost = current_cost;
        //direction_var = current_dir_index;
        continue;
      } else {
        current_x[current_dir_index] = best_x[current_dir_index];  // restore previous value
      }
    }
      // Else variable is Arith
    else {
      double best_step = 0;
      double best_x_i = best_x[current_dir_index];
      for (int candidate_index = 0; candidate_index < 4; ++candidate_index) {
        // Try to increment x[current_dir_index] by step_size  
        double step = step_size[current_dir_index] * candidate[candidate_index];
        current_x[current_dir_index] = best_x[current_dir_index] + step;

        // If integer type, cast to int
        if (is_integer_term(terms, v[current_dir_index])) {
          current_x[current_dir_index] = (int) current_x[current_dir_index];
        }

        // If current_x equal to 
        if (current_x[current_dir_index] == best_x[current_dir_index]) {
          continue;
        }

        if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
          printf("\n increase by %f", step);
          printf("\n current_x[%d] <- %d", current_dir_index, (int) current_x[current_dir_index]);
        }

        current_cost = l2o_evaluate_term_approx(l2o, n_var, v, current_x, t);
        n_calls++;
        if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
          printf("\n current_cost: %.20f", current_cost);
        }
        if (current_cost < best_cost - IMPROVEMENT_THRESHOLD) {
          has_improved = true;
          //best_x[current_dir_index] = current_x[current_dir_index];
          best_step = step;
          best_x_i = current_x[current_dir_index];
          best_cost = current_cost;
          //direction_var = current_dir_index;
        }
      }
      if (best_step == 0) {
        current_x[current_dir_index] = best_x[current_dir_index];  // restore previous value
        step_size[current_dir_index] = step_size[current_dir_index] / acceleration;     // decelerate
      } else {
        if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
          printf("\n best_step: %.20f", best_step);
        }
        current_x[current_dir_index] = best_x_i;   // keep best x found
        best_x[current_dir_index] = current_x[current_dir_index];   // update best_x 
        step_size[current_dir_index] = best_step;   // keep successful acceleration   
        has_improved = true;
      }
    }
    if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
      printf("\n\n has_improved: %d", has_improved);
    }
    if (!has_improved) {    // Go to next var
      current_dir = current_dir->next;
      current_dir_index = current_dir->elem;
      n_var_visited += 1;
    } else {
      n_var_visited = 0;
    }

  }
  if (trace_enabled(l2o->tracer, "mcsat::hill_climbing")) {
    printf("\n\n final_cost: %.50f", best_cost);
  }
  return best_x;
}