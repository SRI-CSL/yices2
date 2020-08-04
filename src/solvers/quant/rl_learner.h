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


#ifndef __RL_LEARNER_H
#define __RL_LEARNER_H

#include "solvers/quant/quant_cnstr.h"

typedef struct learner_s {
  generic_heap_t cnstr_heap;   // heap with cnstr indices in priority order
  uint32_t seed;               // random seed
  uint32_t epsilon;            // in range 0 - (RL_EPSILON_MAX-1)
  double alpha;                // learning rate

  ivector_t latest_cnstr;        // constraints asserted in the latest ematch round
  double latest_reward;         // reward for the latest ematch round

  quant_table_t *qtbl;         // link to quant table
} learner_t;

#define RL_EPSILON_MAX              1000
#define RL_EPSILON_DEFAULT          150
#define RL_ALPHA_DEFAULT            0.1
#define RL_INITIAL_Q_DEFAULT        100

#define RL_TERM_COST_FACTOR         0.3
#define RL_LEMMA_COST_FACTOR        0.1
#define RL_DECISION_COST_FACTOR     1
#define RL_BACKTRACK_REWARD_FACTOR  2

/*
 * Setup learner: iterate over each quant cnstr and setup initial priorities
 */
extern void learner_setup(learner_t *learner);

/*
 * Reset learner stats for ematch round
 */
extern void learner_reset_round(learner_t *learner, bool reset);

/*
 * Update learner stats/rewards for the last ematch round
 */
extern void learner_update_last_round(learner_t *learner, bool update_heap);


/*
 * Update learner term reward for the constraint i
 */
extern void learner_update_term_reward(learner_t *learner, uint32_t cost, uint32_t i);

/*
 * Update learner lemma reward for the constraint i
 */
extern void learner_update_lemma_reward(learner_t *learner, uint32_t cost, uint32_t i);

/*
 * Update learner decision cost (negative rewards) for the latest ematch round
 */
extern void learner_update_decision_reward(learner_t *learner);

/*
 * Update learner backtrack reward for the latest ematch round
 */
extern void learner_update_backtrack_reward(learner_t *learner, uint32_t jump);

/*
 * Add constraint to learner for the latest ematch round
 */
extern void learner_add_cnstr(learner_t *learner, uint32_t i);


/*
 * Initialize learner
 */
extern void init_learner(learner_t *learner, quant_table_t *qtbl);

/*
 * Reset learner
 */
extern void reset_learner(learner_t *learner);

/*
 * Delete learner
 */
extern void delete_learner(learner_t *learner);


#endif /* __RL_LEARNER_H */
