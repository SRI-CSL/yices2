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

#include "plugin.h"
#include "value.h"

#include "utils/scope_holder.h"
#include "mcsat/utils/value_hash_map.h"

/** Nodes in the graph have IDs, this is the type */
typedef uint32_t equality_graph_node_id;

/** Node in the equality graph */
typedef struct equality_graph_node_s {
  /** Id of the representative */
  equality_graph_node_id find;
  /** Next node in the class */
  equality_graph_node_id next;
  /** Index of the term (positive) or value (negative) */
  int32_t index;
  /** Is it a value */
  bool is_value;
} equality_graph_node_t;

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

  /** Vector to store values */
  value_vector_t values_list;

  /** List of the terms added in order */
  ivector_t terms_list;

  /** Scope holder for push/pop */
  scope_holder_t scope_holder;

  /** Name of the equality graph */
  const char* name;

  /** 
   * The data holding the nodes in the graph:
   * - terms are in graph_nodes[0 .. ] */
  equality_graph_node_t* graph_nodes;

  /** Size of the graph nodes */
  uint32_t size;

  /** Capacity of the graph nodes */
  uint32_t capacity;

  /** The plugin context */
  plugin_context_t* ctx;

} equality_graph_t;


/** Construct a new named equality graph. */
void equality_graph_construct(equality_graph_t* eq, plugin_context_t* ctx, const char* name);

/** Destruct the graph */
void equality_graph_destruct(equality_graph_t* eq);

/** Add the term to the database (returns true if newly added). */
bool equality_graph_add_term(equality_graph_t* eq, term_t t);

/** Add the value to the database (value managed outside and must survive until pop). */
bool equality_graph_add_value(equality_graph_t* eq, const mcsat_value_t* v);

/** Is the term already in the graph */
bool equality_graph_has_term(const equality_graph_t* eq, variable_t t);

/** Is the value already in the graph */
bool equality_graph_has_value(const equality_graph_t* eq, const mcsat_value_t* v);

/** Push the context */
void equality_graph_push(equality_graph_t* eq);

/** Pop the context */
void equality_graph_pop(equality_graph_t* eq);

/** Print the equality graph */
void equality_graph_print(const equality_graph_t* eq, FILE* out);

