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
 * Parameters for SAT solver heuristics
 */

#ifndef __SAT_PARAMETERS_H
#define __SAT_PARAMETERS_H

#include <limits.h>


/*
 * Activity threshold and constants for decision heuristic
 * and for recording clause activity.
 */
#define VAR_DECAY_FACTOR         0.95
#define CLAUSE_DECAY_FACTOR      0.999F

#define VAR_ACTIVITY_THRESHOLD        (1e100)
#define INV_VAR_ACTIVITY_THRESHOLD    (1e-100)

#define CLAUSE_ACTIVITY_THRESHOLD     (1e20f)
#define INV_CLAUSE_ACTIVITY_THRESHOLD (1e-20f)

#define INIT_VAR_ACTIVITY_INCREMENT     1.0
#define INIT_CLAUSE_ACTIVITY_INCREMENT  1.0

/*
 * Default random_factor = 2% of decisions are random (more or less)
 * - the heuristic generates a random 24 bit integer
 * - if that number is <= random_factor * 2^24, then a random variable
 *   is chosen
 * - so we store random_factor * 2^24 = random_factor * 0x1000000 in
 *   the randomness field of a sat solver.
 */
#define VAR_RANDOM_FACTOR 0.02F

// mask to extract 24 bits out of an unsigned 32bit integer
#define VAR_RANDOM_MASK  ((uint32_t)0xFFFFFF)
#define VAR_RANDOM_SCALE (VAR_RANDOM_MASK+1)


/*
 * Minimal number of conflicts between two successive calls to
 * simplify_clause_database
 */
#define SIMPLIFY_CONFLICT_THRESHOLD    2000


/*
 * Restart parameters:
 * - Minisat-style: start with RESTART_THRESHOLD then increase geometrically
 * - Picosat-style: inner loop/outer loop both use geometric progression
 *   the inner loop counter is reset to RESTART_THRESHOLD on every
 *   iteration of the outer loop
 * - Luby style: use the sequence 1, 1, 2, 1 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
 *   multiply by the base LUBY_INTERVAL defined below
 *
 * As of 2013/10/04: best setting found is Luby style, with base interval - 10
 */
#define INITIAL_RESTART_THRESHOLD  50   // number of conflicts before the first restart
#define MINISAT_RESTART_FACTOR 1.5      // increase factor for the restart threshold

// Picosat-style restart and reduce
#define RESTART_FACTOR 1.05
#define MAX_DTHRESHOLD 1000000

// Luby-style restart
#define LUBY_INTERVAL 10


/*
 * Heuristic for deletion of half the learned clauses
 * - changed on 2013/09/19: use linear rather than geometric increment
 * - first reduce is when the number of learned clause reaches INIT_REDUCE_THRESHOLD
 * - then after every call to reduce, the threshold is increased by INCR_REDUCE_THRESHOLD
 */
#define INITIAL_REDUCE_THRESHOLD 10000
#define INCR_REDUCE_THRESHOLD  5000

// older version: not used anymore
#define MIN_REDUCE_THRESHOLD 1000       // minimum initial threshold
#define MINISAT_REDUCE_FACTOR 1.1       // increase factor for the threshold

// picosat-stye
#define REDUCE_FACTOR  1.05

/*
 * Parameters for removing irrelevant learned clauses
 * (zchaff-style).
 */
#define TAIL_RATIO 16
#define HEAD_ACTIVITY 500
#define TAIL_ACTIVITY 10
#define HEAD_RELEVANCE 6
#define TAIL_RELEVANCE 45
#define DELETION_PERIOD 5000


#endif /* __SAT_PARAMETERS_H */
