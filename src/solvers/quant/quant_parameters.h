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
 * QUANT SOLVER PARAMETERS
 */


#ifndef __QUANT_PARAMETERS_H
#define __QUANT_PARAMETERS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>
#include <string.h>

/*
 * Tags identifying the iteration order
 */
typedef enum {
  ITERATE_UNKNOWN = -1,
  ITERATE_ALL = 0,
  ITERATE_EPSILONGREEDY = 1,
  ITERATE_RANDOM = 2,
  ITERATE_GREEDY = 3,
} iterate_kind_t;


/*
 * Default bounds for ematching instantiation
 */
#define DEFAULT_MAX_INSTANCES_PER_ROUND   10
#define DEFAULT_MAX_INSTANCES_PER_SEARCH  100
#define DEFAULT_MAX_INSTANCES             100000

#define DEFAULT_MAX_ROUNDS_PER_SEARCH     30
#define DEFAULT_MAX_SEARCH                5000

#define DEFAULT_EMATCH_MODE              ITERATE_EPSILONGREEDY


/*
 * Default bounds ematching execution/trial
 */
#define DEF_INITIAL_FDEPTH  12
#define DEF_INITIAL_VDEPTH  5
#define DEF_MAX_FDEPTH      120
#define DEF_MAX_VDEPTH      50
#define DEF_MAX_FAPPS       5
#define DEF_MAX_MATCHES     1


/*
 * Default parameters for ematching constraint learner
 */
#define CNSTR_RL_ALPHA_DEFAULT            0.1
#define CNSTR_RL_EPSILON_MAX              1000
#define CNSTR_RL_EPSILON_MIN              200
#define CNSTR_RL_EPSILON_DEF              999
#define CNSTR_RL_EPSILON_DECAY            0.999
#define CNSTR_RL_EPSILON_DECAY_ROUNDS     1

#define CNSTR_RL_INITIAL_Q_DEFAULT        100
#define CNSTR_RL_TERM_COST_FACTOR         1
#define CNSTR_RL_LEMMA_COST_FACTOR        0.1
#define CNSTR_RL_DECISION_COST_FACTOR     1
#define CNSTR_RL_BACKTRACK_REWARD_FACTOR  2


/*
 * Default parameters for ematching term learner
 */
#define TERM_RL_ALPHA_DEFAULT                   0.1
#define TERM_RL_EPSILON_MAX                     1000
#define TERM_RL_EPSILON_MIN                     200
#define TERM_RL_EPSILON_DEF                     999
#define TERM_RL_EPSILON_DECAY                   0.999
#define TERM_RL_EPSILON_DECAY_ROUNDS            1

#define TERM_RL_INITIAL_Q_DEFAULT               100
#define TERM_RL_INITIAL_Q_EXTEND_COST_FACTOR    0.1
#define TERM_RL_UNMATCH_COST_FACTOR             0.2
#define TERM_RL_MATCH_REWARD_FACTOR             0.6
#define TERM_RL_DECISION_COST_FACTOR            1
#define TERM_RL_BACKTRACK_REWARD_FACTOR         4
#define TERM_RL_DEPTH_COST_FACTOR               0.8


/*
 * Test whether ematch mode is known and supported.
 * - mode = ematch iteration mode to use
 * - return mode (as positive integer) if this mode is supported.
 * - return -1 otherwise.
 */
extern int32_t supported_ematch_mode(const char *mode);




#endif /* __QUANT_PARAMETERS_H */
