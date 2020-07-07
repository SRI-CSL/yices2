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
 * SOLVER FOR FUNCTION/ARRAY THEORY
 */

/*
 * The solver maintains a graph: vertices denote arrays and edges
 * represent array updates. An edge x ---> y labeled with terms (i_1, ..., i_n)
 * means that x and y must be equal, except possibly at point (i_1,...,i_n).
 */

#ifndef __FUN_SOLVER_H
#define __FUN_SOLVER_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "context/context_types.h"
#include "solvers/cdcl/smt_core.h"
#include "solvers/egraph/diseq_stacks.h"
#include "solvers/egraph/egraph.h"
#include "solvers/funs/fun_level.h"
#include "terms/types.h"
#include "utils/bitvectors.h"
#include "utils/int_hash_map2.h"
#include "utils/int_vectors.h"
#include "utils/ptr_vectors.h"



/*
 * GRAPH/VARIABLES
 */

/*
 * Edges: one edge for each update term.
 * (update f i_1 ... i_n v) creates an edge x ---> y labeled by i_1,.., i_n
 * where source x = variable with term[x] = f
 *       target y = variable with term[y] = (update f i_1 ... i_n v)
 */
typedef struct fun_edge_s {
  thvar_t source;
  thvar_t target;
  occ_t index[0]; // real size = arity n of source and target
} fun_edge_t;


/*
 * Edge table:
 * - resizable array: nedges = number of actual edges
 * - data[i] = pointer to descriptor for edge i
 */
typedef struct fun_edgetable_s {
  uint32_t size;
  uint32_t nedges;
  fun_edge_t **data;
} fun_edgetable_t;

#define DEF_FUN_EDGETABLE_SIZE  100
#define MAX_FUN_EDGETABLE_SIZE  (UINT32_MAX/8)



/*
 * Special edge indices:
 * - null_fun_edge = -1
 * - null_fun_pred = large index (used as a mark as pred[x] when x is a source variable)
 */
enum {
  null_fun_edge = -1,
  null_fun_pred = INT32_MAX,
};



/*
 * Variable table
 * - each variable is a vertex in the graph
 * - for each variable x we store
 *     type[x] = its type (as an index in the type table)
 *    arity[x] = arity as defined by type[x] (not clear this is useful)
 *     fdom[x] = one bit: fdom[x] = 1 iff x has a finite domain
 *    eterm[x] = corresponding egraph term
 *    edges[x] = vector of edge indices (edges with x as an extremity)
 * - these structures are set when the graph and variables are constructed
 *
 * For constructing array models and generating axiom instances:
 * - we group variables into equivalence classes:
 *   x and y are in the same class if eterm[x] and eterm[y] are equal in the egraph
 * - we use a breadth-first exploration of the graph from a source node z
 * The following structures are used:
 *    root[x] = root variable in the same equivalence class as x
 *    next[x] = next element in the same class as x (or null if x is last)
 *     pre[x] = last edge on a path from z to x (identified by its edge id)
 *    base[x] = label to identify connected components: base[x] = base[y] means
 *              that x and y are connected in the graph
 *     app[x] = if x is a root, vector of composite terms (used for model construction)
 *    mark[x] = bit used in propagation
 */
typedef struct fun_vartable_s {
  uint32_t size;
  uint32_t nvars;
  // static
  type_t *type;
  uint32_t *arity;
  byte_t *fdom;
  eterm_t *eterm;
  int32_t **edges;
  // dynamic
  thvar_t *root;
  thvar_t *next;
  int32_t *pre;
  int32_t *base;
  void ***app;
  byte_t *mark;
} fun_vartable_t;


#define DEF_FUN_VARTABLE_SIZE 100
#define MAX_FUN_VARTABLE_SIZE (UINT32_MAX/8)



/*
 * Queue for visiting the graph from a source node
 * - data[0 ... top-1] = visited vertices (data[0] = source)
 * - ptr = next node to process
 * - size = size of the data array
 * If x is and x != source, then pre[x] = k such that edge[k] is the last
 * edge from the path source ... y ---> x. pre[x] = -1 otherwise.
 */
typedef struct fun_queue_s {
  uint32_t size;
  uint32_t top;
  uint32_t ptr;
  thvar_t *data;
} fun_queue_t;

#define DEF_FUN_QUEUE_SIZE 20
#define MAX_FUN_QUEUE_SIZE (UINT32_MAX/4)




/*
 * PUSH/POP STACK
 */

/*
 * Trailer stack:
 * - for every push: keep number of variables + number of edges
 */
typedef struct fun_trail_s {
  uint32_t nvars;
  uint32_t nedges;
} fun_trail_t;

typedef struct fun_trail_stack_s {
  uint32_t size;
  uint32_t top;
  fun_trail_t *data;
} fun_trail_stack_t;

#define DEF_FUN_TRAIL_SIZE 20
#define MAX_FUN_TRAIL_SIZE (UINT32_MAX/sizeof(fun_trail_t))



/*
 * STATISTICS
 */
typedef struct fun_solver_stats_s {
  // initial size
  uint32_t num_init_vars;
  uint32_t num_init_edges;

  // number of axioms generated
  uint32_t num_update_axiom1;
  uint32_t num_update_axiom2;
  uint32_t num_extensionality_axiom;
} fun_solver_stats_t;



/*
 * FULL SOLVER
 */
typedef struct fun_solver_s {
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
  fun_solver_stats_t stats;

  /*
   * Search parameters
   * - bound on the number of update conflicts generated in each call to final_check
   * - bound on the number of extensionality axioms generated in reconcile_model
   */
  uint32_t max_update_conflicts;
  uint32_t max_extensionality;

  /*
   * Main components
   */
  fun_vartable_t vtbl;
  fun_edgetable_t etbl;
  fun_queue_t queue;
  diseq_stack_t dstack;

  /*
   * Push/pop stack
   */
  fun_trail_stack_t trail_stack;

  /*
   * Buffers
   */
  ivector_t aux_vector;
  ivector_t lemma_vector;
  pvector_t app_vector;


  /*
   * apps_ready = true if the app_vectors are available and normalized
   * bases_ready = true if the bases are set
   */
  bool apps_ready;
  bool bases_ready;


  /*
   * reconciled = true if the solver model agrees with the egraph
   * - if this flag is true then we have to ensure that two variables
   *   in different classes are mapped to different arrays in the model.
   * - if this flag is false, then it's possible that two equal array
   *   variables are in different egraph classes.
   */
  bool reconciled;

  /*
   * Components used for interface equalities/model building
   * - num_bases = number of connected components:
   *   for every root variable x base[x] is between 0 and num_bases-1
   * - base_value[i] encodes the default value assigned to every array
   *   variable x such that base[x] = i.
   * The base_value for i is either the label of an egraph term u or a special
   * code (a negative integer). All variables with the same base have a type
   * [domain --> sigma] and base_value[i] denotes some object of type sigma.
   * (Note: all variables have the same type).
   * - base_value[i] can be an egraph class of type sigma: in this
   *   case. We set base_value[i] = label of some class (>= 0)
   * - base_value[i] can be a fresh object of type sigma (i.e., a fresh
   *   particle in the pstore. We encode this by setting base_value[i] = -(k+1)
   *   for some non-negative index k.
   *
   * We use the following rules to assign base_values:
   * - If sigma is infinite, we  can assign a fresh value to base_value[i]
   *   (i.e., a value distinct from that of any other object in the egraph).
   *   This is encoded by setting base[i] = - (i+1).
   * - If sigma is finite, we search for distinct egraph terms (as many as we can)
   *   and use them as base values. If there are not enough egraph terms, then
   *   we create fresh_values (but we make sure the total number of elements
   *   used as base values is not more than card(sigma)). The fresh values
   *   are encoded as negative integers in the range [-p... -1] where
   *   p = card(sigma).
   *
   * When building the model, we convert the base values to particles.
   * For a finite type, sigma we must make sure that all base values with
   * the same negative index are converted to the same fresh particle.
   * To support this, we allocate a hash map if needed.
   */
  uint32_t num_bases;
  int32_t *base_value;

  /*
   * Model:
   * - value[x] = map for variable x
   * - base_map[i] = default map for all variables x such that base[x] = i
   * Value and base_map are allocated only when the model is constructed
   * For robustness, we store the size of these two arrays when they are allocated.
   * We can then delete at any time without having to worry about changes in
   * the number of variables or number of bases.
   */
  map_t **value;
  map_t **base_map;
  uint32_t value_size;
  uint32_t base_map_size;

  /*
   * Hash map used to convert integer codes to fresh particles (for finite types).
   */
  int_hmap2_t *fresh_hmap;

} fun_solver_t;



/*
 * Default bounds
 */
#define DEFAULT_MAX_UPDATE_CONFLICTS 20
#define DEFAULT_MAX_EXTENSIONALITY    1




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
extern void init_fun_solver(fun_solver_t *solver, smt_core_t *core,
                            gate_manager_t *gates, egraph_t *egraph, type_table_t *ttbl);


/*
 * Delete the solver
 */
extern void delete_fun_solver(fun_solver_t *solver);


/*
 * Get the control interface
 */
extern th_ctrl_interface_t *fun_solver_ctrl_interface(fun_solver_t *solver);

/*
 * Get the egraph interfaces
 */
extern th_egraph_interface_t *fun_solver_egraph_interface(fun_solver_t *solver);
extern fun_egraph_interface_t *fun_solver_fun_egraph_interface(fun_solver_t *solver);




/*******************************
 *  INTERNALIZATION FUNCTIONS  *
 ******************************/

/*
 * These functions are exported for testing only.
 * They are used via the funsolver_interface.
 */

/*
 * Create a new array variable.
 * - tau = its type in the solver's internal type table
 */
extern thvar_t fun_solver_create_var(fun_solver_t *solver, type_t tau);

/*
 * Attach egraph term t to array variable v
 */
extern void fun_solver_attach_eterm(fun_solver_t *solver, thvar_t v, eterm_t t);

/*
 * Get the egraph term attached to v
 */
static inline eterm_t fun_solver_eterm_of_var(fun_solver_t *solver, thvar_t v) {
  assert(0 <= v && v < solver->vtbl.nvars);
  return solver->vtbl.eterm[v];
}



/***********************
 *  CONTROL FUNCTIONS  *
 **********************/

/*
 * These functions are used by the egraph. They are declared here for testing.
 */

/*
 * Prepare for search after internalization.
 */
extern void fun_solver_start_search(fun_solver_t *solver);

/*
 * Perform a round of propagations (do nothing)
 */
extern bool fun_solver_propagate(fun_solver_t *solver);

/*
 * Final check
 * - find necessary instances of the array axioms and add them to the egraph.
 * - return FCHECK_SAT if no instance is generated, FCHECK_CONTINUE otherwise.
 */
extern fcheck_code_t fun_solver_final_check(fun_solver_t *solver);


/*
 * Start a new decision level
 */
extern void fun_solver_increase_decision_level(fun_solver_t *solver);

/*
 * Backtrack to back level
 */
extern void fun_solver_backtrack(fun_solver_t *solver, uint32_t back_level);

/*
 * Push/pop/reset
 */
extern void fun_solver_push(fun_solver_t *solver);
extern void fun_solver_pop(fun_solver_t *solver);
extern void fun_solver_reset(fun_solver_t *solver);



/********************************
 *  EGRAPH INTERFACE FUNCTIONS  *
 *******************************/

/*
 * Assert that x1 and x2 are equal
 * - id = edge index to be used in a subsequent call to egraph_explain_term_eq
 * - x1 and x2 are two variables attached to two egraph terms t1 and t2
 * - this function is called when t1 and t2 become equal in the egraph
 */
extern void fun_solver_assert_var_eq(fun_solver_t *solver, thvar_t x1, thvar_t x2, int32_t id);


/*
 * Assert that x1 and x2 are distinct
 * - x1 and x2 are two variables attached to two egraph terms t1 and t2
 * - this function is called when t1 and t2 become distinct in the egraph
 */
extern void fun_solver_assert_var_diseq(fun_solver_t *solver, thvar_t x1, thvar_t x2, composite_t *hint);


/*
 * Assert that all variables a[0] ... a[n-1] are pairwise distinct
 * - they are attached to egraph terms t[0] ... t[n-1]
 * - the function is called when (distinct t[0] ... t[n-1]) is asserted in the egraph
 */
extern void fun_solver_assert_var_distinct(fun_solver_t *solver, uint32_t n, thvar_t *a, composite_t *hint);


/*
 * Check whether x1 and x2 are distinct at the base level
 */
extern bool fun_solver_check_disequality(fun_solver_t *solver, thvar_t x1, thvar_t x2);





/**********************
 *  MODEL GENERATION  *
 *********************/

/*
 * These functions are exported for testing only.
 * The egraph uses the fun_egraph interface.
 */

/*
 * Assign a map to all root variables
 * - each map is of type map_t *
 * - it's built as a map from abstract values to abstract values (particles)
 * - all particles used in the construction must be created in store
 */
extern void fun_solver_build_model(fun_solver_t *solver, pstore_t *store);


/*
 * Return the map assigned to theory variable x
 * - that's the map of root[x]
 * - return NULL if the construction fails in some way
 */
extern map_t *fun_solver_value_in_model(fun_solver_t *solver, thvar_t x);


/*
 * Free all internal structures used in the model construction
 */
extern void fun_solver_free_model(fun_solver_t *solver);




/***************************
 *  SET THE SEARCH BOUNDS  *
 **************************/

/*
 * Max number of extensionality instances (per call to reconcile model)
 */
static inline void fun_solver_set_max_extensionality(fun_solver_t *solver, uint32_t n) {
  assert(n > 0);
  solver->max_extensionality = n;
}

static inline uint32_t fun_solver_get_max_extensionality(fun_solver_t *solver) {
  return solver->max_extensionality;
}


/*
 * Maximal number of update axiom (per call to final_check)
 */
static inline void fun_solver_set_max_update_conflicts(fun_solver_t *solver, uint32_t n) {
  assert(n > 0);
  solver->max_update_conflicts = n;
}

static inline uint32_t fun_solver_get_max_update_conflicts(fun_solver_t *solver) {
  return solver->max_update_conflicts;
}



/****************
 *  STATISTICS  *
 ***************/

/*
 * Number of variables and edges
 */
static inline uint32_t fun_solver_num_vars(fun_solver_t *solver) {
  return solver->stats.num_init_vars;
}

static inline uint32_t fun_solver_num_edges(fun_solver_t *solver) {
  return solver->stats.num_init_edges;
}

/*
 * Number of instances of each axiom
 */
static inline uint32_t fun_solver_num_update1_axioms(fun_solver_t *solver) {
  return solver->stats.num_update_axiom1;
}

static inline uint32_t fun_solver_num_update2_axioms(fun_solver_t *solver) {
  return solver->stats.num_update_axiom2;
}

static inline uint32_t fun_solver_num_extensionality_axioms(fun_solver_t *solver) {
  return solver->stats.num_extensionality_axiom;
}


/********************************
 *  GARBAGE COLLECTION SUPPORT  *
 *******************************/

/*
 * Mark all types used by solver (protect them from deletion in type_table_gc)
 * - scan the variable table and mark every type in table->type[x]
 */
extern void fun_solver_gc_mark(fun_solver_t *solver);



#endif /* __FUN_SOLVER_H */
