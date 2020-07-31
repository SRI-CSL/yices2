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
 * REINFORCEMENT LEARNER
 */


#include "solvers/quant/rl_learner.h"
#include "utils/index_vectors.h"
#include "utils/prng.h"


#define TRACE 0



/*
 * Comparison function:
 * - x and y are two cnstr indices in qtbl
 * - table is a quant cnstr table
 * - return true if x is cheaper to eliminate than y
 */
static bool cmp_cnstr(void *table, int32_t x, int32_t y) {
  quant_table_t *qtbl;
  cnstr_stats_t *xstat, *ystat;

  qtbl = table;

  assert(x >= 0 && x < qtbl->nquant);
  assert(y >= 0 && y < qtbl->nquant);

  xstat = &qtbl->data[x].stats;
  ystat = &qtbl->data[y].stats;

  return xstat->Q > ystat->Q;
}


/*
 * Setup learner: iterate over each quant cnstr and add to heap
 */
void learner_setup(learner_t *learner) {
 quant_table_t *qtbl;
 uint32_t i, n, npat;
 quant_cnstr_t *cnstr;
 generic_heap_t *heap;

 qtbl = learner->qtbl;
 heap = &learner->cnstr_heap;
 n = qtbl->nquant;

 assert(qtbl != NULL);

 for(i=0; i<n; i++) {
   cnstr = qtbl->data + i;
   npat = iv_len(cnstr->patterns);
   if (npat != 0) {
     generic_heap_add(heap, i);
   }
 }

}


/*
 * Reset learner stats for ematch round
 */
void learner_reset_round(learner_t *learner, bool reset) {
  if (reset) {
    ivector_reset(&learner->latest_cnstr);
  }

  learner->latest_reward = 0;
#if TRACE
  printf("  New reward (reset) = %.2f\n", learner->latest_reward);
#endif
}


/*
 * Update learner stats/rewards for the last ematch round
 */
void learner_update_last_round(learner_t *learner, bool update_heap) {
  quant_table_t *qtbl;
  uint32_t i, n, cIdx;
  ivector_t *latest_cnstr;
  quant_cnstr_t *cnstr;

  if (update_heap || learner->latest_reward != 0) {
    qtbl = learner->qtbl;
    latest_cnstr = &learner->latest_cnstr;
    n = latest_cnstr->size;

    for(i=0; i<n; i++) {
      cIdx = latest_cnstr->data[i];
      assert(cIdx < qtbl->nquant);

      cnstr = qtbl->data + cIdx;

      if (learner->latest_reward != 0) {
        cnstr->stats.Q += learner->alpha * (learner->latest_reward - cnstr->stats.Q);
#if TRACE
        printf("  New reward (cumulative) for cnstr @%d = %.2f\n", cIdx, learner->latest_reward);
#endif
      }

      if (update_heap) {
        generic_heap_update(&learner->cnstr_heap, cIdx);
      }
    }

    learner->latest_reward = 0;
  }
}


/*
 * Update learner lemma reward for the constraint i
 */
void learner_update_lemma_reward(learner_t *learner, uint32_t cost, uint32_t i) {
  quant_table_t *qtbl;
  quant_cnstr_t *cnstr;
  double reward;

  qtbl = learner->qtbl;
  assert(i < qtbl->nquant);

  cnstr = qtbl->data + i;
  reward = (- RL_LEMMA_COST_FACTOR * cost);

  cnstr->stats.Q += learner->alpha * (reward - cnstr->stats.Q);
#if TRACE
  printf("  New reward (lemma) for cnstr @%d = %.2f\n", i, reward);
#endif
}

/*
 * Update learner decision cost (negative rewards) for the latest ematch round
 */
void learner_update_decision_reward(learner_t *learner) {
  double reward;

  if (learner->latest_cnstr.size != 0) {
    reward = (- RL_DECISION_COST_FACTOR);
    learner->latest_reward += reward;
#if TRACE
    printf("  New reward (decision) = %.2f\n", reward);
#endif
  }
}

/*
 * Update learner backtrack reward for the latest ematch round
 */
void learner_update_backtrack_reward(learner_t *learner, uint32_t jump) {
  double reward;

  if (learner->latest_cnstr.size != 0) {
    reward = (RL_BACKTRACK_REWARD_FACTOR * jump);
    learner->latest_reward += reward;
#if TRACE
    printf("  New reward (backtrack) = %.2f\n", reward);
#endif

    learner_update_last_round(learner, false);
  }

}

/*
 * Add constraint to learner for the latest ematch round
 */
void learner_add_cnstr(learner_t *learner, uint32_t i) {
  ivector_push(&learner->latest_cnstr, i);
}


/*
 * Initialize learner
 */
void init_learner(learner_t *learner, quant_table_t *qtbl) {
  init_generic_heap(&learner->cnstr_heap, 0, 0, cmp_cnstr, qtbl);

  learner->qtbl = qtbl;
  learner->seed = PRNG_DEFAULT_SEED;
  learner->epsilon = RL_EPSILON_DEFAULT;
  learner->alpha = RL_ALPHA_DEFAULT;

  init_ivector(&learner->latest_cnstr, 10);
}


/*
 * Reset learner
 */
void reset_learner(learner_t *learner) {
  reset_generic_heap(&learner->cnstr_heap);
  ivector_reset(&learner->latest_cnstr);
}


/*
 * Delete learner
 */
void delete_learner(learner_t *learner) {
  delete_generic_heap(&learner->cnstr_heap);

  learner->qtbl = NULL;

  delete_ivector(&learner->latest_cnstr);
}
