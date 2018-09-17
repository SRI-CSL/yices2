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

#include "terms/term_manager.h"

/**
 * Traditional functionality:
 * - Add terms to the term database
 * - Assert terms are equal/disequal (merge)
 * 
 * We use terms as the representation for terms in order to accomodate 
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

  /** Term manager */
  term_manager_t tm;

  /** File to output the graph when debugging */
  FILE* graph_out;

  /** Explanation id */
  uint32_t explain_id;

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
 * Add an uninterpreted function term to the database (if not there) and
 * return id. This will also run propagation. If the term was added before
 * as a regular term, it will be now treated as a function. You can associate
 * several different functions to the same term.
 *
 * @param t the full term itself (e.g., f(x, y, 1))
 * @param f the function symbold (e.g. f)
 * @param the direct subterms of the term including the function itself
 *        (e.g., [x, y, 1]).
 */
eq_node_id_t eq_graph_add_ufun_term(eq_graph_t* eq, term_t t, term_t f, uint32_t n, const term_t* children);

/**
 * Add an interpreted function term to the database (if not there) and
 * return id. This will also run propagation. If the term was added before
 * as a regular term, it will be now treated as a function. You can associate
 * several different functions to the same term.
 *
 * @param t the full term itself (e.g., f(x, y, 1))
 * @param f the function symbol (e.g. EQ_TERM)
 * @param the direct subterms of the term including the function itself
 *        (e.g., [x, y, 1]).
 */
eq_node_id_t eq_graph_add_ifun_term(eq_graph_t* eq, term_t t, term_kind_t f, uint32_t n, const term_t* children);

/** Is the term already in the graph */
bool eq_graph_has_term(const eq_graph_t* eq, term_t t);

/** Get the ID of a term (assumes that it exists) */
eq_node_id_t eq_graph_term_id(const eq_graph_t* eq, term_t t);

/** Get the ID of a term (returns null node if not there) */
eq_node_id_t eq_graph_term_id_if_exists(const eq_graph_t* eq, term_t t);

/** Push the context */
void eq_graph_push(eq_graph_t* eq);

/** Pop the context */
void eq_graph_pop(eq_graph_t* eq);

/** Print the equality graph */
void eq_graph_print(const eq_graph_t* eq, FILE* out);

/** Assert equality lhs = rhs with given polarity and associated reason. Runs propagation. **/
void eq_graph_assert_term_eq(eq_graph_t* eq, term_t lhs, term_t rhs, uint32_t reason_data);

/** Is there any propagated terms */
bool eq_graph_has_propagated_terms(const eq_graph_t* eq);

/** Get the terms that have been deduced equal and clear them (call once) */
void eq_graph_get_propagated_terms(eq_graph_t* eq, ivector_t* out_terms);

/** Get the value of a propagated term */
const mcsat_value_t* eq_graph_get_propagated_term_value(const eq_graph_t* eq, term_t t);

/** Propagate the trail */
void eq_graph_propagate_trail(eq_graph_t* eq);

/** Returns true if the trail is fully propagated */
bool eq_graph_is_trail_propagated(const eq_graph_t* eq);

/**
 * Explain the reported conflict. Returns sequence of reason data, and
 * associated types. The only returned data is for types that have associated
 * data and terms that evaluate to true in trail. Pass NULL for types if you
 * don't care about types.
 */
void eq_graph_get_conflict(const eq_graph_t* eq, ivector_t* conflict_data, ivector_t* conflict_types);

/**
 * Explain a term propagation, i.e., why term is equal to a value. The only
 * returned data is for types that have associated data and terms that evaluate
 * to true in trail. Pass NULL for types if you don't care about types.
 *
 * Returns the substitution term
 */
term_t eq_graph_explain_term_propagation(const eq_graph_t* eq, term_t t, ivector_t* explain_data, ivector_t* explain_types);

/** Mark all terms (as variables). */
void eq_graph_gc_mark_all_terms(const eq_graph_t* eq, gc_info_t* gc_vars);
