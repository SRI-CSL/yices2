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

/** Reason for merge (users should use >= 0, negative reserved for internal use */
typedef int32_t eq_reason_t;

typedef enum {
  EQ_NODE_TERM,   // Nodes for representing a term
  EQ_NODE_VALUE,  // Nodes for representing a value
  EQ_NODE_PAIR    // Nodes for represenging a pair of other nodes
} eq_node_type_t;

/** Node in the equality graph */
typedef struct eq_node_s {

  /** Type of the node */
  eq_node_type_t type;

  /** Id of the representative */
  eq_node_id_t find;
  /** Next node in the class */
  eq_node_id_t next;
  /** Index of the term in it's list */
  uint32_t index;
  /** Is it a constant */
  bool is_constant;

} eq_node_t;

/** Edges in the graph have IDs, this is the type */
typedef uint32_t eq_edge_id_t;

#define eq_edge_null ((eq_edge_id_t) -1)

/** An edge (u, v) in the graph */
typedef struct eq_graph_edge_s {
  /** Edge goes to node v */
  eq_node_id_t v;
  /** Reason of the edge */
  eq_reason_t reason;
  /** Next edge */
  eq_edge_id_t next;
} eq_edge_t;
