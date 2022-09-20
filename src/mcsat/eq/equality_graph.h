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

#pragma once

#include <mcsat/utils/value_hash_map.h>
#include <mcsat/utils/value_vector.h>
#include <stdbool.h>

#include "mcsat/plugin.h"
#include "mcsat/value.h"

#include "mcsat/utils/scope_holder.h"
#include "mcsat/utils/value_hash_map.h"

#include "equality_graph_types.h"
#include "merge_queue.h"

#include "utils/pair_hash_map2.h"
#include "utils/ptr_vectors.h"

#include "terms/term_manager.h"

typedef struct {
  eq_node_id_t n; // The node to be examined
  eq_edge_id_t e; // The edge we traversed to get here
  uint32_t prev; // Index of previous node in the queue
} bfs_entry_t;

typedef struct {
  bfs_entry_t* data;
  uint32_t size;
  uint32_t capacity;
} bfs_vector_t;

/** API calls */
typedef enum {
  EQ_GRAPH_ADD_TERM, // Add a term (e.g. x)
  EQ_GRAPH_ADD_UFUN, // Add a term with children (e.g., f(x))
  EQ_GRAPH_ADD_IFUN, // Add a term with children (e.g., (x = y))
  EQ_GRAPH_PROPAGATE_TRAIL, // Run propagation of trail
  EQ_GRAPH_ASSERT_EQ // Assert user added equality
} eq_graph_api_type_t;

/**
 * Traditional functionality:
 * - Add terms to the term database
 * - Assert terms are equal/disequal (merge)
 * 
 * We use terms as the representation for terms in order to accommodate 
 * for plugins adding terms that are not in the variable database (e.g., 
 * bit-vector slicing).
 * 
 * MCSAT specific functionality:
 * - Assert term is equal/disequal to value
 * - Values are managed outside
 * - Garbage collection: remove unmarked terms
 * - Push/pop:
 *   - removes assertions 
 *   - removes values
 *   - remove terms
 */
typedef struct eq_graph_s {

  /** Map from interpreted functions to id */
  int_hmap_t kind_to_id;

  /** Map from terms to id */
  int_hmap_t term_to_id;

  /** Map from values to id */
  value_hmap_t value_to_id;

    /** Map from pairs to ids */
  pmap2_t pair_to_id;

  /** Map from eqality pairs to ids */
  pmap2_t eq_pair_to_id;

  /** List of the kinds added in order */
  ivector_t kind_list;

  /** List of the terms added in order */
  ivector_t terms_list;

  /** Vector to store values */
  value_vector_t values_list;

  /** List of pairs added in order */
  ivector_t pair_list;

  /** Scope holder for push/pop */
  scope_holder_t scope_holder;

  /** Name of the equality graph */
  const char* name;

  /* The graph nodes */
  eq_node_t* nodes;

  /** Size of the graph nodes */
  uint32_t nodes_size;

  /** Capacity of the graph nodes */
  uint32_t nodes_capacity;

  /** The graph edges in order of addition */
  eq_edge_t* edges;

  /** Size of the graph nodes */
  uint32_t edges_size;

  /** Capacity of the graph nodes */
  uint32_t edges_capacity;

  /** The graph itself (map from node to the last inserted edge) */
  ivector_t graph;

  /** The hash map of function pair representatives. */
  pmap2_t pair_to_rep;

  /** The hash map of equality pair representatives. */
  pmap2_t eq_pair_to_rep;

  /** The plugin context */
  plugin_context_t* ctx;

  /** Queue for merging */
  merge_queue_t merge_queue;

  /** List of merged nodes in pairs (into, from) */
  ivector_t merges;

  /** Lock when we're in propagation */
  bool in_propagate;

  /** Flag indicating a conflict */
  bool in_conflict;

  /** We have a conflict when two constant nodes are merged, these are the nodes */
  eq_node_id_t conflict_lhs, conflict_rhs;

  /**
   * We don't notify on deductions, instead the user can get the terms
   * that are deduced to be equal to a constant.
   */
  ivector_t term_value_merges;

  /** Last processed trail index */
  uint32_t trail_i;

  /** The use-list data */
  eq_uselist_t* uselist_nodes;

  /** Size of the use-list memory */
  uint32_t uselist_nodes_size;

  /** The capacity of the use-list memory */
  uint32_t uselist_nodes_capacity;

  /** The actual uselist per node */
  ivector_t uselist;

  /** Map from arrays to their updates */
  ptr_hmap_t array_to_updates;

  /** Map from arrays to app terms that read the respectice array */
  ptr_hmap_t array_to_reads;

  /** Map from indices to app terms that read at the respective index */
  ptr_hmap_t idx_to_reads;

  /** Map from temr types to app terms with the corresponding domain */
  ptr_hmap_t idxtype_to_arrays;

  /** Map from types to diff symbols */
  int_hmap_t type_to_diff;

  /** Chronological list uf uselist updates */
  ivector_t uselist_updates;

  /** Vector for storing function children */
  ivector_t children_list;

  /** Map from nodes to their children (if any) */
  int_hmap_t node_to_children;

  /** True node (value) */
  eq_node_id_t true_node_id;

  /** False node (value) */
  eq_node_id_t false_node_id;

  /** File to output the graph when debugging */
  FILE* graph_out;

  /** Explanation id */
  uint32_t explain_id;

  /** The queue for doing BFS */
  bfs_vector_t bfs_queue;

  /** Log of API calls */
  ivector_t api_log;

  /** Cache of explanations */
  ivector_t explain_cache_list;

  /** Map from explain pairs to index in the explain cache */
  pmap2_t explain_cache_map;

} eq_graph_t;

/** Construct a new named equality graph. */
void eq_graph_construct(eq_graph_t* eq, plugin_context_t* ctx, const char* name);

/** Destruct the graph */
void eq_graph_destruct(eq_graph_t* eq);

/** Add the term to the database (if not there) and return id. Runs propagation. */
eq_node_id_t eq_graph_add_term(eq_graph_t* eq, term_t t);

/** Returns the number of terms in the graph */
uint32_t eq_graph_term_size(const eq_graph_t* eq);

/**
 * Adds an update term (e.g., update a x y) where the value a[x] is updated to y
 *
 * @param t the full term itself
 * @param array_t the array term that gets updated
 * @param n the number of children
 * @param children the direct subterms of the term
 * @return eq_node_id_t
 */
eq_node_id_t eq_graph_add_update_term(eq_graph_t *eq, term_t t, term_t arr_t, uint32_t n, const term_t *children);

/**
 * Add an uninterpreted function term to the database (if not there) and
 * return id. This will also run propagation. If the term was added before
 * as a regular term, it will be now treated as a function. You can associate
 * several different functions to the same term.
 *
 * @param t the full term itself (e.g., f(x, y, 1))
 * @param f the function symbol  (e.g. f)
 * @param children the direct subterms of the term including the function itself
 *        (e.g., [f, x, y, 1]).
 */
eq_node_id_t eq_graph_add_ufun_term(eq_graph_t* eq, term_t t, term_t f, uint32_t n, const term_t* children);

/**
 * Add an interpreted function term to the database (if not there) and
 * return id. This will also run propagation. If the term was added before
 * as a regular term, it will be now treated as a function. You can associate
 * several different functions to the same term.
 *
 * @param t the full term itself (e.g., rdiv x y)
 * @param k the kind of t (e.g. ARITH_RDIV)
 * @param n number of children of t (e.g. 2)
 * @param the direct subterms of the term (e.g., [x, y]).
 */
eq_node_id_t eq_graph_add_ifun_term(eq_graph_t* eq, term_t t, term_kind_t k, uint32_t n, const term_t* children);

/** Is the term already in the graph */
bool eq_graph_has_term(const eq_graph_t* eq, term_t t);

/** Are those terms in the same class (i.e. equal). Assumes graph has the 2 terms. */
bool eq_graph_are_equal(const eq_graph_t* eq, term_t t1, term_t t2);

/** Does this term have a value in the graph? */
bool eq_graph_term_has_value(const eq_graph_t* eq, term_t t);

/** Get the ID of a term (assumes that it exists) */
eq_node_id_t eq_graph_term_id(const eq_graph_t* eq, term_t t);

/** Get the ID of a term (returns null node if not there) */
eq_node_id_t eq_graph_term_id_if_exists(const eq_graph_t* eq, term_t t);

/** Returns true if term is a representative of its class */
bool eq_graph_term_is_rep(const eq_graph_t* eq, term_t t);

/** Push the context */
void eq_graph_push(eq_graph_t* eq);

/** Pop the context */
void eq_graph_pop(eq_graph_t* eq);

/** Print the equality graph */
void eq_graph_print(const eq_graph_t* eq, FILE* out);

/** Assert equality lhs = rhs with given polarity and associated reason. Runs propagation. **/
void eq_graph_assert_term_eq(eq_graph_t* eq, term_t lhs, term_t rhs, uint32_t reason_data);

/** Assert assignment t *= v with associated reason. Runs propagation. **/
void eq_graph_assign_term_value(eq_graph_t* eq, term_t t, const mcsat_value_t* v, uint32_t reason_data);
  
/** Is there any propagated terms */
bool eq_graph_has_propagated_terms(const eq_graph_t* eq);

/**
 * Get the terms that have been deduced equal and clear them (call once).
 * Argument out_terms can be NULL if you want to clear the propagated terms.
 */
void eq_graph_get_propagated_terms(eq_graph_t* eq, ivector_t* out_terms);

/** Does the term have propagated value */
bool eq_graph_has_propagated_term_value(const eq_graph_t* eq, term_t t);

/** Get the value of a propagated term. */
const mcsat_value_t* eq_graph_get_propagated_term_value(const eq_graph_t* eq, term_t t);

/** Propagate the trail */
void eq_graph_propagate_trail(eq_graph_t* eq);

/** Propagate individual assertion */
void eq_graph_propagate_trail_assertion(eq_graph_t* eq, term_t atom);

/** Returns true if the trail is fully propagated */
bool eq_graph_is_trail_propagated(const eq_graph_t* eq);

/**
 * Explain the reported conflict. Returns sequence of reason data, and
 * associated types. The only returned data is for types that have associated
 * data and terms that evaluate to true in trail. Pass NULL for types if you
 * don't care about types.
 */
void eq_graph_get_conflict(const eq_graph_t* eq, ivector_t* conflict_data, ivector_t* conflict_types, int_mset_t* terms_used);

/**
 * Explain why two terms are equal. Returns sequence of reason data, and
 * associated types. The only returned data is for types that have associated
 * data and terms that evaluate to true in trail. Pass NULL for types if you
 * don't care about types.
 */
void eq_graph_explain_eq(const eq_graph_t* eq, term_t t1, term_t t2, ivector_t* reasons_data, ivector_t* reasons_types, int_mset_t* terms_used);
  
/**
 * Explain a term propagation, i.e., why term is equal to a value. The only
 * returned data is for types that have associated data and terms that evaluate
 * to true in trail. Pass NULL for types if you don't care about types.
 *
 * Returns the substitution term
 */
term_t eq_graph_explain_term_propagation(const eq_graph_t* eq, term_t t, ivector_t* explain_data, ivector_t* explain_types, int_mset_t* terms_used);

typedef enum {
  EQ_GRAPH_MARK_ALL, // Mark all terms with variables, and their children
  EQ_GRAPH_MARK_ASSIGNED // Mark all terms assigned/asserted, and their children
} eq_graph_marking_type_t;

/**
 * Mark the minimal set of variables needed to maintain the deductions:
 * - variables of terms asserted in the trail
 * - variables of terms asserted by the user
 * - children of any marked terms
 */
void eq_graph_gc_mark(const eq_graph_t* eq, gc_info_t* gc_vars, eq_graph_marking_type_t type);

/**
 * Get list of forbidden values (by disequalitites) for term t. If
 * values != NULL it will be filled with forbidden values. Result is true
 * if v != NULL or v != from all values.
 */
bool eq_graph_get_forbidden(const eq_graph_t* eq, term_t t, pvector_t* values, const mcsat_value_t* v);
