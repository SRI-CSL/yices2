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

#include <stdbool.h>

/** Nodes in the graph have IDs, this is the type */
typedef uint32_t eq_node_id_t;

#define eq_node_null ((eq_node_id_t) -1)

typedef enum {
  REASON_IS_FUNCTION_DEF,      // f(x, y) = (f (x y)), no data
  REASON_IS_CONSTANT_DEF,      // term(5) = value(5), no data
  REASON_IS_CONGRUENCE,        // x = y -> f(x) = f(y), no data
  REASON_IS_CONGRUENCE_EQ_SYM, // special case of congruence for equality with symmetry
  REASON_IS_TRUE_EQUALITY,     // (x = y) = true ->  x = y, data = eq id
  REASON_IS_REFLEXIVITY,       // x = y -> (x = y) = true, data = eq id
  REASON_IS_EVALUATION,        // x = v1, y = v2 -> (x = y) = false, data = eq id
  REASON_IS_IN_TRAIL,          // trail propagated, data = term that evaluates to true in trail
  REASON_IS_USER,              // Asserted by user
  REASON_IS_READ_OF_UPDATE,    // Read at an index that has been updated before
  REASON_IS_UNAFFECTED_UPDATE, // Read at a different position than a write
} eq_reason_type_t;

/** Reason for a deduction/assertion */
typedef struct eq_reason_s {
  eq_reason_type_t type; // Type of reason
  uint32_t data;         // Aux data
} eq_reason_t;

typedef enum {
  EQ_NODE_KIND,     // Nodes for representing interpreted functions (kinds)
  EQ_NODE_TERM,     // Nodes for representing a term
  EQ_NODE_VALUE,    // Nodes for representing a value
  EQ_NODE_PAIR,     // Nodes for representing a pair of other nodes
  EQ_NODE_EQ_PAIR, // Nodes for representing an equality
} eq_node_type_t;

typedef uint32_t eq_uselist_id_t;

#define eq_uselist_null ((eq_uselist_id_t) -1)

/** Element of the use-list */
typedef struct eq_uselist_s {
  eq_node_id_t node;    // The node
  eq_uselist_id_t next; // The rest of the list
} eq_uselist_t;

/** Node in the equality graph */
typedef struct eq_node_s {

  /** Type of the node */
  eq_node_type_t type;
  /** Size of the equivalence class */
  uint32_t size;

  /** Id of the representative */
  eq_node_id_t find;
  /** Next node in the class */
  eq_node_id_t next;
  /** Index of the term in it's list */
  uint32_t index;

  /** Uselist for this node */
  eq_uselist_id_t uselist;

} eq_node_t;

/** Edges in the graph have IDs, this is the type */
typedef uint32_t eq_edge_id_t;

#define eq_edge_null ((eq_edge_id_t) -1)

/** An edge (u, v) in the graph */
typedef struct eq_graph_edge_s {
  /** Edge from u to v */
  eq_node_id_t u, v;
  /** Reason of the edge */
  eq_reason_t reason;
  /** Next edge */
  eq_edge_id_t next;
} eq_edge_t;
