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
 * SOLVER FOR QUANTIFIERS
 */


#ifndef __QUANT_SOLVER_H
#define __QUANT_SOLVER_H


#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "context/context_types.h"
#include "solvers/cdcl/smt_core.h"
#include "solvers/egraph/diseq_stacks.h"
#include "solvers/egraph/egraph.h"
#include "terms/types.h"
#include "utils/bitvectors.h"
#include "utils/int_hash_map2.h"
#include "utils/int_vectors.h"
#include "utils/ptr_vectors.h"
#include "solvers/quant/ef_problem.h"
#include "solvers/quant/quant_ematching.h"
#include "solvers/quant/rl_learner.h"


/*
 * STATISTICS
 */
typedef struct quant_solver_stats_s {
  // initial size
  uint32_t num_quantifiers;
  uint32_t num_patterns;

  uint32_t num_instances;             // number of instances generated (total)
  uint32_t num_instances_per_search;  // number of instances generated per search
  uint32_t num_instances_per_round;   // number of instanced generated in each call to final_check

  uint32_t num_rounds_per_search;     // number of rounds of ematching run per search
  uint32_t num_search;                // number of searches

  uint32_t max_instances;             // max number of instances generated (total)
  uint32_t max_instances_per_search;  // max number of instances generated per search
  uint32_t max_instances_per_round;   // max number of instanced generated in each call to final_check

  uint32_t max_rounds_per_search;     // max number of rounds of ematching run per search
  uint32_t max_search;                // max number of searches
} quant_solver_stats_t;


/*
 * Tags identifying the iteration order
 */
typedef enum {
  ITERATE_ALL,
  ITERATE_RANDOM,
  ITERATE_GREEDY,
  ITERATE_EPSILONGREEDY,
} iterate_kind_t;


/*
 * Default bounds
 */
#define DEFAULT_MAX_INSTANCES_PER_ROUND   10
#define DEFAULT_MAX_INSTANCES_PER_SEARCH  100
#define DEFAULT_MAX_INSTANCES             100000

#define DEFAULT_MAX_ROUNDS_PER_SEARCH     50
#define DEFAULT_MAX_SEARCH                5000

#define DEFAULT_ITERATE_MODE              ITERATE_EPSILONGREEDY


/*
 * FULL SOLVER
 */
typedef struct quant_solver_s {
  /*
   * Attached core + egraph + gate manager + type table
   */
  smt_core_t *core;
  gate_manager_t *gate_manager;
  egraph_t *egraph;
  type_table_t *types;

  /*
   * Base level/decision level
   */
  uint32_t base_level;
  uint32_t decision_level;

  /*
   * Statistics
   */
  quant_solver_stats_t stats;

  /*
   * Main components
   */
  ef_prob_t *prob;
  pattern_table_t ptbl;   // pattern table
  quant_table_t qtbl;     // quant table
  ematch_globals_t em;    // ematching

  iterate_kind_t iter_mode;  // iteration mode over constraints
  learner_t learner;         // Reinforce learner

  ivector_t base_literals;
  ivector_t base_antecedents;

  ivector_t round_cnstrs;
  ivector_t round_instances;

// TODO

  /*
   * Buffers
   */
  ivector_t aux_vector;
  ivector_t aux_vector2;
  int_hmap_t aux_map;

} quant_solver_t;





/*********************
 *  MAIN OPERATIONS  *
 ********************/

/*
 * Initialize the function solver
 * - core = attached smt_core
 * - gates = gate manager for the core
 * - egraph = attached egraph
 * - ttbl = attached type table
 */
extern void init_quant_solver(quant_solver_t *solver, smt_core_t *core,
                            gate_manager_t *gates, egraph_t *egraph, type_table_t *ttbl);


/*
 * Delete the solver
 */
extern void delete_quant_solver(quant_solver_t *solver);


/*
 * Get the control interface
 */
extern th_ctrl_interface_t *quant_solver_ctrl_interface(quant_solver_t *solver);

/*
 * Get the egraph interfaces
 */
extern th_egraph_interface_t *quant_solver_egraph_interface(quant_solver_t *solver);
extern quant_egraph_interface_t *quant_solver_quant_egraph_interface(quant_solver_t *solver);
// TODO




/*******************************
 *  INTERNALIZATION FUNCTIONS  *
 ******************************/

/*
 * These functions are exported for testing only.
 * They are used via the quantsolver_interface.
 */
// TODO



/***********************
 *  CONTROL FUNCTIONS  *
 **********************/

/*
 * These functions are used by the egraph. They are declared here for testing.
 */

/*
 * Prepare for search after internalization.
 */
extern void quant_solver_start_search(quant_solver_t *solver);

/*
 * Perform a round of propagations (do nothing)
 */
extern bool quant_solver_propagate(quant_solver_t *solver);

/*
 * Final check
 * - find necessary instances of the quantifier instances and add them to the egraph.
 * - return FCHECK_SAT if no instance is generated, FCHECK_CONTINUE otherwise.
 */
extern fcheck_code_t quant_solver_final_check(quant_solver_t *solver);


/*
 * Start a new decision level
 */
extern void quant_solver_increase_decision_level(quant_solver_t *solver);

/*
 * Backtrack to back level
 */
extern void quant_solver_backtrack(quant_solver_t *solver, uint32_t back_level);

/*
 * Push/pop/reset
 */
extern void quant_solver_push(quant_solver_t *solver);
extern void quant_solver_pop(quant_solver_t *solver);
extern void quant_solver_reset(quant_solver_t *solver);



/********************************
 *  EGRAPH INTERFACE FUNCTIONS  *
 *******************************/
// TODO




/**********************
 *  MODEL GENERATION  *
 *********************/

/*
 * These functions are exported for testing only.
 * The egraph uses the quant_egraph interface.
 */

// TODO



/***************************
 *  SET THE SEARCH BOUNDS  *
 **************************/

/*
 * Maximal number of quantifier instances (per search)
 */
static inline void quant_solver_set_max_instances(quant_solver_t *solver, uint32_t n) {
  assert(n > 0);
  solver->stats.max_instances = n;
}

/*
 * Maximal number of quantifier instances (per call to final_check)
 */
static inline void quant_solver_set_max_instances_per_round(quant_solver_t *solver, uint32_t n) {
  assert(n > 0);
  solver->stats.max_instances_per_round = n;
}


/****************
 *  STATISTICS  *
 ***************/

/*
 * Number of quantifiers
 */
static inline uint32_t quant_solver_num_quantifiers(quant_solver_t *solver) {
  return solver->stats.num_quantifiers;
}

/*
 * Number of patterns
 */
static inline uint32_t quant_solver_num_patterns(quant_solver_t *solver) {
  return solver->stats.num_patterns;
}

/*
 * Number of quantifier instances
 */
static inline uint32_t quant_solver_num_instances(quant_solver_t *solver) {
  return solver->stats.num_instances;
}


/********************************
 *  GARBAGE COLLECTION SUPPORT  *
 *******************************/
// TODO


/*********************
 *  PROBLEM SUPPORT  *
 ********************/

/*
 * Attach problem to solver
 */
extern void quant_solver_attach_prob(quant_solver_t *solver, ef_prob_t *prob, context_t *ctx);



#endif /* __QUANT_SOLVER_H */
