/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * REINFORCEMENT LEARNER FOR TERMS
 */


#ifndef __TERM_LEARNER_H
#define __TERM_LEARNER_H

#include "context/context_types.h"
#include "utils/uint_learner.h"
#include "solvers/quant/quant_parameters.h"


typedef struct term_learner_s {
  uint_learner_t learner;      // learner
  egraph_t *egraph;            // link to egraph
  iterate_kind_t iter_mode;    // iteration mode over terms

  generic_heap_t aux_heap;     // temporary heap with term indices in priority order
  uint32_t max_depth;          // max function depth corresponding to the term stored in learner
  uint32_t min_epsilon;        // min epsilon value
} term_learner_t;


/*
 * Setup learner: iterate over each term and setup initial priorities
 */
extern void term_learner_setup(term_learner_t *learner);

/*
 * Extend setup learner: iterate over each new term and add to heap
 */
extern void term_learner_setup_extend(term_learner_t *learner);


/*
 * Reset learner stats for ematch round
 */
extern void term_learner_reset_round(term_learner_t *learner, bool reset);

/*
 * Update learner stats/rewards for the last ematch round
 */
extern void term_learner_update_last_round(term_learner_t *learner, bool update_heap);


/*
 * Update learner match reward for the term i
 */
extern void term_learner_update_match_reward(term_learner_t *learner, uint32_t i);

/*
 * Update learner unmatch reward for the term i
 */
extern void term_learner_update_unmatch_reward(term_learner_t *learner, uint32_t i);

/*
 * Update learner decision cost (negative rewards) for the latest ematch round
 */
extern void term_learner_update_decision_reward(term_learner_t *learner);

/*
 * Update learner backtrack reward for the latest ematch round
 */
extern void term_learner_update_backtrack_reward(term_learner_t *learner, uint32_t jump);

/*
 * Decrease learner epsilon by decay factor (bounded by minimum value)
 */
extern void term_learner_decay_epsilon(term_learner_t *learner);


/*
 * Add constraint to learner for the latest ematch round
 */
static inline void term_learner_add_latest(term_learner_t *learner, uint32_t i) {
  uint_learner_add_index(&learner->learner, i);
}

/*
 * Reset constraints for the latest ematch round
 */
static inline void term_learner_reset_latest(term_learner_t *learner) {
  uint_learner_reset_indices(&learner->learner);
}


/*
 * Initialize learner
 */
extern void init_term_learner(term_learner_t *learner);

/*
 * Reset learner
 */
extern void reset_term_learner(term_learner_t *learner);

/*
 * Delete learner
 */
extern void delete_term_learner(term_learner_t *learner);


#endif /* __TERM_LEARNER_H */
