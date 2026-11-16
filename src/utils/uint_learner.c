/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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


