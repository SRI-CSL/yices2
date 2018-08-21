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
typedef struct equality_graph_s {

  /** Map from terms to id */
  int_hmap_t term_to_id;

  /** Map from values to id */
  value_hmap_t value_to_id;

  /** Map from pairs to ids */
  pmap2_t pair_to_id;

  /** Vector to store values */
  value_vector_t values_list;

  /** List of the terms added in order */
  ivector_t terms_list;

  /** List of pairs added in order */
  ivector_t pairs_list;

  /** Scope holder for push/pop */
  scope_holder_t scope_holder;

  /** Name of the equality graph */
  const char* name;

  /* The graph nodes */
  equality_graph_node_t* nodes;

  /** Size of the graph nodes */
  uint32_t nodes_size;

  /** Capacity of the graph nodes */
  uint32_t nodes_capacity;

  /** The graph edges in order of addition */
  equality_graph_edge_t* edges;

  /** Size of the graph nodes */
  uint32_t edges_size;

  /** Capacity of the graph nodes */
  uint32_t edges_capacity;

  /** The graph itself (map from node to the last inserted edge) */
  ivector_t graph;

  /** The hash map of pair representatives. */
  pmap2_t pair_to_rep;

  /** The plugin context */
  plugin_context_t* ctx;

  /** Queue for merging */
  merge_queue_t merge_queue;

  /** Lock when we're in propagation */
  bool in_propagate;

  /** Flag indiciating a conflict */
  bool in_conflict;

} equality_graph_t;

/** Construct a new named equality graph. */
void equality_graph_construct(equality_graph_t* eq, plugin_context_t* ctx, const char* name);

/** Destruct the graph */
void equality_graph_destruct(equality_graph_t* eq);

/** Add the term to the database (if not there) and return id. */
equality_graph_node_id_t equality_graph_add_term(equality_graph_t* eq, term_t t);

/**
 * Add a function term to the database (if not there) and return id.
 * @param t the full term itself (e.g., f(x, y, 1))
 * @param the direct subterms of the term including the function itself
 *        (e.g., [f, x, y, 1]).
 */
equality_graph_node_id_t equality_graph_add_function_term(equality_graph_t* eq,
    term_t t, uint32_t n_subterms, const term_t* subterms);

/** Add the value to the database (if not there). */
equality_graph_node_id_t equality_graph_add_value(equality_graph_t* eq, const mcsat_value_t* v);

/** Is the term already in the graph */
bool equality_graph_has_term(const equality_graph_t* eq, variable_t t);

/** Is the value already in the graph */
bool equality_graph_has_value(const equality_graph_t* eq, const mcsat_value_t* v);

/** Get the ID of a term */
equality_graph_node_id_t equality_graph_term_id(const equality_graph_t* eq, term_t t);

/** Get the ID of a value */
equality_graph_node_id_t equality_graph_value_id(const equality_graph_t* eq, const mcsat_value_t* v);

/** Push the context */
void equality_graph_push(equality_graph_t* eq);

/** Pop the context */
void equality_graph_pop(equality_graph_t* eq);

/** Print the equality graph */
void equality_graph_print(const equality_graph_t* eq, FILE* out);

/** Assert equality lhs = rhs with given polarity and associated reason. **/
void equality_graph_assert_eq(equality_graph_t* eq,
    equality_graph_node_id_t lhs,
    equality_graph_node_id_t rhs,
    bool polarity,
    equality_merge_reason_t reason);




