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
 * Setup learner: iterate over each quant cnstr and add to heap
 * - add to heap only when patterns are present
 */
void cnstr_learner_setup(cnstr_learner_t *learner) {
  uint_learner_t *uint_learner;
  quant_table_t *qtbl;
  quant_cnstr_t *cnstr;
  uint32_t i, n, npat;

  generic_heap_t *heap;
  pvector_t *pv;
  uint_learner_stats_t *s;

  uint_learner = &learner->learner;
  qtbl = learner->qtbl;
  assert(qtbl != NULL);

  n = qtbl->nquant;
  heap = &uint_learner->heap;
  pv = &uint_learner->stats;

  reset_uint_learner_stats(uint_learner);

  for(i=0; i<n; i++) {
    s = (uint_learner_stats_t *) safe_malloc(sizeof(uint_learner_stats_t));
    s->Q = uint_learner->initQ;
    pvector_push(pv, s);

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
void cnstr_learner_reset_round(cnstr_learner_t *learner, bool reset) {
  if (reset) {
    uint_learner_reset_indices(&learner->learner);
  }

  uint_learner_reset_reward(&learner->learner);
#if TRACE
  printf("  New reward (reset) = %.2f\n", uint_learner_get_reward(&learner->learner));
#endif
}


/*
 * Update learner stats/rewards for the last ematch round
 */
void cnstr_learner_update_last_round(cnstr_learner_t *learner, bool update_heap) {
  uint_learner_t *uint_learner;
  uint32_t i, n, cIdx;
  ivector_t *latest_cnstr;

  uint_learner = &learner->learner;

  if (update_heap || uint_learner_get_reward(uint_learner) != 0) {
    latest_cnstr = &uint_learner->latest_indices;
    n = latest_cnstr->size;

    for(i=0; i<n; i++) {
      cIdx = latest_cnstr->data[i];
      assert(cIdx < learner->qtbl->nquant);

      if (uint_learner_get_reward(uint_learner) != 0) {
        uint_learner_updateQ_latest(uint_learner, cIdx);

#if TRACE
        printf("  New reward (cumulative) for cnstr @%d = %.2f\n", cIdx, uint_learner_get_reward(uint_learner));
#endif
      }

      if (update_heap) {
        uint_learner_update_heap(uint_learner, cIdx);
      }
    }

    uint_learner_reset_reward(uint_learner);
  }
}


/*
 * Update learner term reward for the constraint i
 */
void cnstr_learner_update_term_reward(cnstr_learner_t *learner, uint32_t cost, uint32_t i) {
  double reward;

  assert(i < learner->qtbl->nquant);

  reward = (- CNSTR_RL_TERM_COST_FACTOR * cost);
  uint_learner_updateQ(&learner->learner, i, reward);

#if TRACE
  printf("  New reward (term) for cnstr @%d = %.2f\n", i, reward);
#endif
}

/*
 * Update learner lemma reward for the constraint i
 */
void cnstr_learner_update_lemma_reward(cnstr_learner_t *learner, uint32_t cost, uint32_t i) {
  double reward;

  assert(i < learner->qtbl->nquant);

  reward = (- CNSTR_RL_LEMMA_COST_FACTOR * cost);
  uint_learner_updateQ(&learner->learner, i, reward);

#if TRACE
  printf("  New reward (lemma) for cnstr @%d = %.2f\n", i, reward);
#endif
}

/*
 * Update learner decision cost (negative rewards) for the latest ematch round
 */
void cnstr_learner_update_decision_reward(cnstr_learner_t *learner) {
  double reward;
  uint_learner_t *uint_learner;

  uint_learner = &learner->learner;

  if (!uint_learner_empty_indices(uint_learner)) {
    reward = (- CNSTR_RL_DECISION_COST_FACTOR);
    uint_learner_add_reward(uint_learner, reward);

#if TRACE
    printf("  New reward (decision) = %.2f\n", reward);
#endif
  }
}

/*
 * Update learner backtrack reward for the latest ematch round
 */
void cnstr_learner_update_backtrack_reward(cnstr_learner_t *learner, uint32_t jump) {
  double reward;
  uint_learner_t *uint_learner;

  uint_learner = &learner->learner;

  if (!uint_learner_empty_indices(uint_learner)) {
    reward = (CNSTR_RL_BACKTRACK_REWARD_FACTOR * jump);
    uint_learner_add_reward(uint_learner, reward);

#if TRACE
    printf("  New reward (backtrack) = %.2f\n", reward);
#endif

    cnstr_learner_update_last_round(learner, false);
  }

}


/*
 * Initialize learner
 */
void init_cnstr_learner(cnstr_learner_t *learner, quant_table_t *qtbl) {
  uint_learner_t *uint_learner;

  uint_learner = &learner->learner;
  init_uint_learner(uint_learner, qtbl->nquant);
  uint_learner_set_epsilon(uint_learner, CNSTR_RL_EPSILON_DEFAULT);
  uint_learner_set_alpha(uint_learner, CNSTR_RL_ALPHA_DEFAULT);
  uint_learner_set_initQ(uint_learner, CNSTR_RL_INITIAL_Q_DEFAULT);

  learner->qtbl = qtbl;
}


/*
 * Reset learner
 */
void reset_cnstr_learner(cnstr_learner_t *learner) {
  reset_uint_learner(&learner->learner);
}


/*
 * Delete learner
 */
void delete_cnstr_learner(cnstr_learner_t *learner) {
  delete_uint_learner(&learner->learner);
  learner->qtbl = NULL;
}
