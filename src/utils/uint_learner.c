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

/*
 * GENERIC REINFORCEMENT LEARNER FOR UNSIGNED INTEGERS
 */


#include "utils/uint_learner.h"
#include "utils/index_vectors.h"
#include "utils/prng.h"
#include <stdio.h>


/*
 * Comparison function:
 * - x and y are two indices in stats vector
 * - return true if x is cheaper than y
 */
static bool cmp_term(void *table, int32_t x, int32_t y) {
  pvector_t *stats;
  uint_learner_stats_t *xstat, *ystat;

  stats = table;

  assert(x >= 0 && x < stats->size);
  assert(y >= 0 && y < stats->size);

  xstat = stats->data[x];
  ystat = stats->data[y];

  return xstat->Q > ystat->Q;
}


/*
 * Reset learner stats vector
 */
void reset_uint_learner_stats(uint_learner_t *learner) {
  pvector_t *pv;
  uint32_t i, n;

  pv = &learner->stats;
  n = pv->size;

  for(i=0; i<n; i++) {
    safe_free(pv->data[i]);
  }
  pvector_reset(pv);
}



/*
 * Initialize learner
 */
void init_uint_learner(uint_learner_t *learner, uint32_t n) {
  init_pvector(&learner->stats, n);
  init_generic_heap(&learner->heap, 0, 0, cmp_term, &learner->stats);

  learner->seed = PRNG_DEFAULT_SEED;
  learner->epsilon = UINT_RL_EPSILON_DEFAULT;
  learner->alpha = UINT_RL_ALPHA_DEFAULT;
  learner->initQ = UINT_RL_INITIAL_Q_DEFAULT;

  init_ivector(&learner->latest_indices, 10);
}


/*
 * Reset learner
 */
void reset_uint_learner(uint_learner_t *learner) {
  reset_generic_heap(&learner->heap);
  ivector_reset(&learner->latest_indices);
  reset_uint_learner_stats(learner);
}


/*
 * Delete learner
 */
void delete_uint_learner(uint_learner_t *learner) {
  delete_generic_heap(&learner->heap);
  delete_ivector(&learner->latest_indices);

  reset_uint_learner_stats(learner);
  delete_pvector(&learner->stats);
}


/*
 * Print index priority
 */
void uint_learner_print_index_priority(uint_learner_t *learner, uint32_t i) {
  uint_learner_stats_t *s;

  assert(i < learner->stats.size);
  s = learner->stats.data[i];

  printf("\tQ(%d) = %.2f\n", i, s->Q);
}

/*
 * Print all indices priority
 */
void uint_learner_print_indices_priority(uint_learner_t *learner, const char *comment) {
  uint32_t i, n;

  printf("  Q values %s:\n", comment);

  n = learner->stats.size;
  for(i=0; i<n; i++) {
    uint_learner_print_index_priority(learner, i);
  }

}


