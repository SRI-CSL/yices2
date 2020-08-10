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
 * REINFORCEMENT LEARNER FOR TERMS
 */


#include "solvers/quant/term_learner.h"
#include "utils/index_vectors.h"
#include "utils/prng.h"


#define TRACE 0



/*
 * Setup learner: iterate over each term and add to heap
 */
void term_learner_setup(term_learner_t *learner) {
  uint_learner_t *uint_learner;
  eterm_table_t *terms;
  uint32_t i, n;

  generic_heap_t *heap;
  pvector_t *pv;
  uint_learner_stats_t *s;

  uint_learner = &learner->learner;
  terms = &learner->egraph->terms;
  assert(terms != NULL);

  n = terms->nterms;
  heap = &uint_learner->heap;
  pv = &uint_learner->stats;

  reset_uint_learner_stats(uint_learner);

  for(i=0; i<n; i++) {
    s = (uint_learner_stats_t *) safe_malloc(sizeof(uint_learner_stats_t));
    s->Q = uint_learner->initQ;
    pvector_push(pv, s);

    generic_heap_add(heap, i);
  }
}

/*
 * Extend setup learner: iterate over each new term and add to heap
 */
void term_learner_setup_extend(term_learner_t *learner) {
  uint_learner_t *uint_learner;
  eterm_table_t *terms;
  uint32_t i, n, oldsz;

  generic_heap_t *heap;
  pvector_t *pv;
  uint_learner_stats_t *s;

  uint_learner = &learner->learner;
  terms = &learner->egraph->terms;
  assert(terms != NULL);

  n = terms->nterms;
  heap = &uint_learner->heap;
  pv = &uint_learner->stats;
  oldsz = pv->size;

  for(i=oldsz; i<n; i++) {
    s = (uint_learner_stats_t *) safe_malloc(sizeof(uint_learner_stats_t));
    s->Q = (TERM_RL_INITIAL_Q_EXTEND_COST_FACTOR * uint_learner->initQ);
    pvector_push(pv, s);

    generic_heap_add(heap, i);
  }
}


/*
 * Reset learner stats for ematch round
 */
void term_learner_reset_round(term_learner_t *learner, bool reset) {
  if (reset) {
    uint_learner_reset_indices(&learner->learner);
  }

  uint_learner_reset_reward(&learner->learner);
#if TRACE
  printf("  New term reward (reset) = %.2f\n", uint_learner_get_reward(&learner->learner));
#endif
}


/*
 * Update learner stats/rewards for the last ematch round
 */
void term_learner_update_last_round(term_learner_t *learner, bool update_heap) {
  uint_learner_t *uint_learner;
  uint32_t i, n, cIdx;
  ivector_t *latest_terms;

  uint_learner = &learner->learner;

  if (update_heap || uint_learner_get_reward(uint_learner) != 0) {
    latest_terms = &uint_learner->latest_indices;
    n = latest_terms->size;

    for(i=0; i<n; i++) {
      cIdx = latest_terms->data[i];
      assert(cIdx < learner->egraph->terms.nterms);

      if (uint_learner_get_reward(uint_learner) != 0) {
        uint_learner_updateQ_latest(uint_learner, cIdx);

#if TRACE
        printf("  New term reward (cumulative) for term @%d = %.2f\n", cIdx, uint_learner_get_reward(uint_learner));
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
 * Update learner match reward for the term i
 */
void term_learner_update_match_reward(term_learner_t *learner, uint32_t i) {
  double reward;

  assert(i < learner->egraph->terms.nterms);

  reward = (TERM_RL_MATCH_REWARD_FACTOR);
  uint_learner_updateQ(&learner->learner, i, reward);

#if TRACE
  printf("  New reward (match) for term @%d = %.2f\n", i, reward);
#endif
}

/*
 * Update learner unmatch reward for the term i
 */
void term_learner_update_unmatch_reward(term_learner_t *learner, uint32_t i) {
  double reward;

  assert(i < learner->egraph->terms.nterms);

  reward = (- TERM_RL_UNMATCH_COST_FACTOR);
  uint_learner_updateQ(&learner->learner, i, reward);

#if TRACE
  printf("  New reward (unmatch) for term @%d = %.2f\n", i, reward);
#endif
}


/*
 * Update learner decision cost (negative rewards) for the latest ematch round
 */
void term_learner_update_decision_reward(term_learner_t *learner) {
  double reward;
  uint_learner_t *uint_learner;

  uint_learner = &learner->learner;

  if (!uint_learner_empty_indices(uint_learner)) {
    reward = (- TERM_RL_DECISION_COST_FACTOR);
    uint_learner_add_reward(uint_learner, reward);

#if TRACE
    printf("  New term reward (decision) = %.2f\n", reward);
#endif
  }
}

/*
 * Update learner backtrack reward for the latest ematch round
 */
void term_learner_update_backtrack_reward(term_learner_t *learner, uint32_t jump) {
  double reward;
  uint_learner_t *uint_learner;

  uint_learner = &learner->learner;

  if (!uint_learner_empty_indices(uint_learner)) {
    reward = (TERM_RL_BACKTRACK_REWARD_FACTOR * jump);
    uint_learner_add_reward(uint_learner, reward);

#if TRACE
    printf("  New term reward (backtrack) = %.2f\n", reward);
#endif

    term_learner_update_last_round(learner, false);
  }

}


/*
 * Initialize learner
 */
void init_term_learner(term_learner_t *learner) {
  uint_learner_t *uint_learner;

  uint_learner = &learner->learner;
  init_uint_learner(uint_learner, 10);
  uint_learner_set_epsilon(uint_learner, TERM_RL_EPSILON_DEFAULT);
  uint_learner_set_alpha(uint_learner, TERM_RL_ALPHA_DEFAULT);
  uint_learner_set_initQ(uint_learner, TERM_RL_INITIAL_Q_DEFAULT);

  learner->egraph = NULL;
  learner->iter_mode = DEFAULT_EMATCH_MODE;

  init_generic_heap(&learner->aux_heap, 0, 0, uint_learner->heap.cmp, &uint_learner->stats);
}

/*
 * Reset learner
 */
void reset_term_learner(term_learner_t *learner) {
  reset_uint_learner(&learner->learner);
  reset_generic_heap(&learner->aux_heap);
}

/*
 * Delete learner
 */
void delete_term_learner(term_learner_t *learner) {
  delete_uint_learner(&learner->learner);
  learner->egraph = NULL;
  delete_generic_heap(&learner->aux_heap);
}


