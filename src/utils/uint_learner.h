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
 * -
 */


#ifndef __UINT_LEARNER_H
#define __UINT_LEARNER_H

#include "utils/generic_heap.h"
#include "utils/int_vectors.h"
#include "utils/ptr_vectors.h"


#define UINT_RL_EPSILON_MAX              1000
#define UINT_RL_EPSILON_DEFAULT          150
#define UINT_RL_ALPHA_DEFAULT            0.1
#define UINT_RL_INITIAL_Q_DEFAULT        100


typedef struct uint_learner_stats_s {
  double Q;
} uint_learner_stats_t;

typedef struct uint_learner_s {
  generic_heap_t heap;         // heap with term indices in priority order
  uint32_t seed;               // random seed
  uint32_t epsilon;            // in range 0 - (RL_EPSILON_MAX-1)
  double alpha;                // learning rate
  double initQ;               // initial Q value

  ivector_t latest_indices;    // indices asserted/involved in the latest round
  double latest_reward;        // reward for the latest round

  pvector_t stats;             // stats vector
} uint_learner_t;


/*
 * Initialize learner
 */
extern void init_uint_learner(uint_learner_t *learner, uint32_t n);

/*
 * Reset learner
 */
extern void reset_uint_learner(uint_learner_t *learner);

/*
 * Delete learner
 */
extern void delete_uint_learner(uint_learner_t *learner);

/*
 * Reset learner stats vector
 */
extern void reset_uint_learner_stats(uint_learner_t *learner);


/*
 * Set learner seed (i.e. random seed)
 */
static inline void uint_learner_set_seed(uint_learner_t *learner, uint32_t seed) {
  learner->seed = seed;
}

/*
 * Get learner seed (i.e. random seed)
 */
static inline uint32_t *uint_learner_get_seed(uint_learner_t *learner) {
  return &learner->seed;
}


/*
 * Set learner epsilon (i.e. exploration chance)
 * - epsilon should be in the range [0 .. UINT_RL_EPSILON_MAX)
 */
static inline void uint_learner_set_epsilon(uint_learner_t *learner, uint32_t epsilon) {
  assert(epsilon < UINT_RL_EPSILON_MAX);
  learner->epsilon = epsilon;
}

/*
 * Get learner epsilon (i.e. exploration chance)
 */
static inline uint32_t uint_learner_get_epsilon(uint_learner_t *learner) {
  return learner->epsilon;
}


/*
 * Set learner alpha (i.e. learning rate)
 * - alpha should be in the range [0 .. 1]
 */
static inline void uint_learner_set_alpha(uint_learner_t *learner, double alpha) {
  assert(alpha >= 0 && alpha <= 1);
  learner->alpha = alpha;
}

/*
 * Get learner alpha (i.e. learning rate)
 * - alpha should be in the range [0 .. 1]
 */
static inline double uint_learner_get_alpha(uint_learner_t *learner) {
  return learner->alpha;
}


/*
 * Set learner initial Q values
 */
static inline void uint_learner_set_initQ(uint_learner_t *learner, double initQ) {
  learner->initQ = initQ;
}

/*
 * Get learner initial Q values
 */
static inline double uint_learner_get_initQ(uint_learner_t *learner) {
  return learner->initQ;
}


/*
 * Set latest reward
 */
static inline void uint_learner_set_reward(uint_learner_t *learner, double reward) {
  learner->latest_reward = reward;
}

/*
 * Get latest reward
 */
static inline double uint_learner_get_reward(uint_learner_t *learner) {
  return learner->latest_reward;
}

/*
 * Add latest reward
 */
static inline void uint_learner_add_reward(uint_learner_t *learner, double reward) {
  learner->latest_reward += reward;
}

/*
 * Reset latest reward
 */
static inline void uint_learner_reset_reward(uint_learner_t *learner) {
  uint_learner_set_reward(learner, 0);
}


/*
 * Update Q value at index i
 */
static inline void uint_learner_updateQ(uint_learner_t *learner, uint32_t i, double reward) {
  pvector_t *pv;
  uint_learner_stats_t *s;

  pv = &learner->stats;
  assert(i < pv->size);

  s = pv->data[i];
  s->Q += learner->alpha * (reward - s->Q);
}

/*
 * Update Q value at index i to latest reward
 */
static inline void uint_learner_updateQ_latest(uint_learner_t *learner, uint32_t i) {
  uint_learner_updateQ(learner, i, learner->latest_reward);
}


/*
 * Reset latest indices
 */
static inline void uint_learner_reset_indices(uint_learner_t *learner) {
  ivector_reset(&learner->latest_indices);
}

/*
 * Add latest indices
 */
static inline void uint_learner_add_index(uint_learner_t *learner, uint32_t i) {
  ivector_push(&learner->latest_indices, i);
}

/*
 * Returns true if latest indices are empty
 */
static inline bool uint_learner_empty_indices(uint_learner_t *learner) {
  return (learner->latest_indices.size == 0);
}

/*
 * Update heap at index i
 */
static inline void uint_learner_update_heap(uint_learner_t *learner, uint32_t i) {
  generic_heap_update(&learner->heap, i);
}


/*
 * Print index priority
 */
extern void uint_learner_print_index_priority(uint_learner_t *learner, uint32_t i);

/*
 * Print all indices priority
 */
extern void uint_learner_print_indices_priority(uint_learner_t *learner, const char *comment);



#endif /* __UINT_LEARNER_H */
