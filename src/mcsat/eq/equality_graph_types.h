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
typedef uint32_t equality_graph_node_id_t;

#define equality_graph_node_null ((equality_graph_node_id) -1)

/** Reason for merge (users should use >= 0, negative reserved for internal use */
typedef int32_t equality_merge_reason_t;

/** Node in the equality graph */
typedef struct equality_graph_node_s {
  /** Id of the representative */
  equality_graph_node_id_t find;
  /** Next node in the class */
  equality_graph_node_id_t next;
  /** Index of the term (positive) or value (negative) */
  int32_t index;
  /** Is it a value */
  bool is_value;
  /** Is it a constant */
  bool is_constant;
} equality_graph_node_t;

/** Edges in the graph have IDs, this is the type */
typedef uint32_t equality_graph_edge_id_t;

#define equality_graph_edge_null ((equality_graph_edge_id) -1)

/** An edge (u, v) in the graph */
typedef struct equality_graph_edge_s {
  /** Edge goes to node v */
  equality_graph_node_id_t v;
  /** Reason of the edge */
  equality_merge_reason_t reason;
  /** Next edge */
  equality_graph_edge_id_t next;
} equality_graph_edge_t;
