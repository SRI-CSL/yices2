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
 * REINFORCEMENT LEARNER FOR QUANT CONSTRAINTS
 */


#ifndef __CNSTR_LEARNER_H
#define __CNSTR_LEARNER_H

#include "solvers/quant/quant_cnstr.h"
#include "utils/uint_learner.h"
#include "solvers/quant/quant_parameters.h"


typedef struct cnstr_learner_s {
  uint_learner_t learner;      // learner
  quant_table_t *qtbl;         // link to quant table
  iterate_kind_t iter_mode;    // iteration mode over constraints
  uint32_t min_epsilon;        // min epsilon value
} cnstr_learner_t;


/*
 * Setup learner: iterate over each quant cnstr and setup initial priorities
 */
extern void cnstr_learner_setup(cnstr_learner_t *learner);

/*
 * Reset learner stats for ematch round
 */
extern void cnstr_learner_reset_round(cnstr_learner_t *learner, bool reset);

/*
 * Update learner stats/rewards for the last ematch round
 */
extern void cnstr_learner_update_last_round(cnstr_learner_t *learner, bool update_heap);


/*
 * Update learner term reward for the constraint i
 */
extern void cnstr_learner_update_term_reward(cnstr_learner_t *learner, uint32_t cost, uint32_t i);

/*
 * Update learner lemma reward for the constraint i
 */
extern void cnstr_learner_update_lemma_reward(cnstr_learner_t *learner, uint32_t cost, uint32_t i);

/*
 * Update learner decision cost (negative rewards) for the latest ematch round
 */
extern void cnstr_learner_update_decision_reward(cnstr_learner_t *learner);

/*
 * Update learner backtrack reward for the latest ematch round
 */
extern void cnstr_learner_update_backtrack_reward(cnstr_learner_t *learner, uint32_t jump);

/*
 * Decrease learner epsilon by decay factor (bounded by minimum value)
 */
extern void cnstr_learner_decay_epsilon(cnstr_learner_t *learner);


/*
 * Add constraint to learner for the latest ematch round
 */
static inline void cnstr_learner_add_cnstr(cnstr_learner_t *learner, uint32_t i) {
  uint_learner_add_index(&learner->learner, i);
}

/*
 * Reset constraints for the latest ematch round
 */
static inline void cnstr_learner_reset_cnstr(cnstr_learner_t *learner) {
  uint_learner_reset_indices(&learner->learner);
}


/*
 * Initialize learner
 */
extern void init_cnstr_learner(cnstr_learner_t *learner, quant_table_t *qtbl);

/*
 * Reset learner
 */
extern void reset_cnstr_learner(cnstr_learner_t *learner);

/*
 * Delete learner
 */
extern void delete_cnstr_learner(cnstr_learner_t *learner);


#endif /* __CNSTR_LEARNER_H */
