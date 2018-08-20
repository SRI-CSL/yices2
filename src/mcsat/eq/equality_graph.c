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

#include "equality_graph.h"
#include "utils/memalloc.h"
#include "mcsat/tracing.h"

#include <inttypes.h>
#include <assert.h>

void equality_graph_construct(equality_graph_t* eq, plugin_context_t* ctx, const char* name) {
  eq->ctx = ctx;

  eq->nodes_capacity = 0;
  eq->nodes_size = 0;
  eq->nodes = NULL;

  eq->edges_capacity = 0;
  eq->edges_size = 0;
  eq->edges = NULL;

  eq->name = name;

  eq->in_conflict = false;
  eq->in_propagate = false;

  init_int_hmap(&eq->term_to_id, 0);
  init_value_hmap(&eq->value_to_id, 0);
  init_ivector(&eq->terms_list, 0);
  init_value_vector(&eq->values_list, 0);
  init_merge_queue(&eq->merge_queue, 0);
  init_ivector(&eq->graph, 0);

  scope_holder_construct(&eq->scope_holder);

  // Add true/false
  equality_graph_add_value(eq, &mcsat_value_true);
  equality_graph_add_value(eq, &mcsat_value_false);
}

void equality_graph_destruct(equality_graph_t* eq) {
  safe_free(eq->nodes);
  safe_free(eq->edges);

  delete_int_hmap(&eq->term_to_id);
  delete_value_hmap(&eq->value_to_id);
  delete_ivector(&eq->terms_list);
  delete_value_vector(&eq->values_list);
  delete_merge_queue(&eq->merge_queue);
  delete_ivector(&eq->graph);
}

// Default initial size and max size
#define DEFAULT_GRAPH_SIZE 10
#define MAX_GRAPH_SIZE (UINT32_MAX/sizeof(equality_graph_node_t))

#define DEFAULT_EDGES_SIZE 10
#define MAX_EDGES_SIZE (UINT32_MAX/sizeof(equality_graph_edge_t))

static
equality_graph_node_t* equality_graph_new_node(equality_graph_t* eq) {
  uint32_t n = eq->nodes_size;

  // Check if we need to resize
  if (n == eq->nodes_capacity) {
    // Compute new size
    if (n == 0) {
      n = DEFAULT_GRAPH_SIZE;
    } else {
      n ++;
      n += n >> 1;
      if (n >= MAX_GRAPH_SIZE) {
        out_of_memory();
      }
    }
    // Resize
    eq->nodes = (equality_graph_node_t*) safe_realloc(eq->nodes, n * sizeof(equality_graph_node_t));
    eq->nodes_capacity = n;
  }

  // Return the new element
  return &eq->nodes[eq->nodes_size ++];
}

equality_graph_node_id_t equality_graph_add_term(equality_graph_t* eq, term_t t) {

  // New id of the node
  equality_graph_node_id_t id = eq->nodes_size;
  uint32_t index = eq->terms_list.size;

  // Check if already there
  int_hmap_pair_t* find = int_hmap_get(&eq->term_to_id, t);
  if (find->val < 0) {
    find->val = id;
    ivector_push(&eq->terms_list, t);
  } else {
    return find->val;
  }

  // Setup the new node
  equality_graph_node_t* node = equality_graph_new_node(eq);
  node->find = id;
  node->next = id;
  node->index = index;
  node->is_value = false;
  node->is_constant = is_const_term(eq->ctx->terms, t);

  assert(eq->terms_list.size + eq->values_list.size == eq->nodes_size);

  // Added, done
  return id;
}

equality_graph_node_id_t equality_graph_add_value(equality_graph_t* eq, const mcsat_value_t* v) {

  // New id of the node
  equality_graph_node_id_t id = eq->nodes_size;
  uint32_t index = eq->values_list.size;

  // Check if already there
  value_hmap_pair_t* find = value_hmap_get(&eq->value_to_id, v);
  if (find->val < 0) {
    find->val = id;
    value_vector_push(&eq->values_list);
    mcsat_value_t* v_copy = value_vector_last(&eq->values_list);
    mcsat_value_assign(v_copy, v);
  } else {
    return find->val;
  }

  // Setup the new node
  equality_graph_node_t* node = equality_graph_new_node(eq);
  node->find = id;
  node->next = id;
  node->index = index;
  node->is_value = true;
  node->is_constant = true;

  assert(eq->terms_list.size + eq->values_list.size == eq->nodes_size);

  // Added, done
  return id;
}

equality_graph_node_id_t equality_graph_term_id(const equality_graph_t* eq, term_t t) {
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &eq->term_to_id, t);
  assert(find != NULL);
  return find->val;
}

equality_graph_node_id_t equality_graph_value_id(const equality_graph_t* eq, const mcsat_value_t* v) {
  value_hmap_pair_t* find = value_hmap_find(&eq->value_to_id, v);
  assert(find != NULL);
  return find->val;
}

bool equality_graph_has_term(const equality_graph_t* eq, variable_t t) {
  return int_hmap_find((int_hmap_t*) &eq->term_to_id, t) != NULL;
}

bool equality_graph_has_value(const equality_graph_t* eq, const mcsat_value_t* v) {
  return value_hmap_find(&eq->value_to_id, v) != NULL;
}

void equality_graph_push(equality_graph_t* eq) {
  scope_holder_push(&eq->scope_holder,
      &eq->terms_list.size,
      &eq->values_list.size,
      NULL
  );
}

void equality_graph_pop(equality_graph_t* eq) {
  uint32_t term_list_size, value_list_size;

  scope_holder_pop(&eq->scope_holder,
      &term_list_size,
      &value_list_size,
      NULL
  );

  // TODO: actually remove data
  assert(false);
}

void equality_graph_print_class(const equality_graph_t* eq, equality_graph_node_id_t start_node_id, FILE* out) {
  const equality_graph_node_t* n = eq->nodes + start_node_id;
  bool first = true;
  do {
    if (!first) { fprintf(out, ", "); }
    if (n->is_value) {
      const mcsat_value_t* v = eq->values_list.data + n->index;
      uint32_t n_id = n - eq->nodes;
      mcsat_value_print(v, out);
      fprintf(out, "(id=%"PRIu32", idx=%"PRIu32")", n->index, n_id);
    } else {
      term_t t = eq->terms_list.data[n->index];
      uint32_t n_id = n - eq->nodes;
      term_print_to_file(out, eq->ctx->terms, t);
      fprintf(out, "(id=%"PRIu32", idx=%"PRIu32")", n->index, n_id);
    }
    n = eq->nodes + n->next;
    first = false;
  } while (n->index != start_node_id);
}

void equality_graph_print(const equality_graph_t* eq, FILE* out) {
  uint32_t i;

  // Print all the terms
  for (i = 0; i < eq->terms_list.size; ++ i) {
    term_t t = eq->terms_list.data[i];
    term_print_to_file(out, eq->ctx->terms, t);
    fprintf(out, " (%"PRIu32"): ", i);
    equality_graph_node_id_t t_id = equality_graph_term_id(eq, t);
    equality_graph_print_class(eq, t_id, out);
    fprintf(out, "\n");
  }

  // Print all the values
  for (i = 0; i < eq->values_list.size; ++ i) {
    const mcsat_value_t* v = eq->values_list.data + i;
    mcsat_value_print(v, out);
    fprintf(out, " (%"PRIu32"): ", i);
    uint32_t v_id = equality_graph_value_id(eq, v);
    equality_graph_print_class(eq, v_id, out);
    fprintf(out, "\n");
  }
}

/** Merge node n2 into n1 */
static
void equality_graph_merge(equality_graph_t* eq, equality_graph_node_id_t n1_id, equality_graph_node_id_t n2_id) {

  equality_graph_node_t* n1 = eq->nodes + n1_id;
  equality_graph_node_t* n2 = eq->nodes + n2_id;

  assert(n1->find == n1_id);
  assert(n1->find == n2_id);
  assert(n1_id != n2_id);

  // Update the find in n2's class
  do {
    n2->find = n1->find;
    n2 = eq->nodes + n2->next;
  } while (n2->find != n1->find);

  // Finally merge the lists (circular lists)
  equality_graph_node_id_t tmp = n1->next;
  n1->next = n2->next;
  n2->next = tmp;
}

/** Do we prefer n1 to n2 */
static inline
bool equality_graph_merge_preference(const equality_graph_node_t* n1, const equality_graph_node_t* n2) {

  // If n1 is a constant then yes
  if (n1->is_constant) {
    return true;
  }

  // Otherwise we don't prefer n1 (we don't care)
  return false;
}

/** Allocate a new edge */
static
equality_graph_edge_t* equality_graph_new_edge(equality_graph_t* eq) {
  uint32_t n = eq->edges_size;

  // Check if we need to resize
  if (n == eq->edges_capacity) {
    // Compute new size
    if (n == 0) {
      n = DEFAULT_EDGES_SIZE;
    } else {
      n ++;
      n += n >> 1;
      if (n >= MAX_EDGES_SIZE) {
        out_of_memory();
      }
    }
    // Resize
    eq->edges = (equality_graph_edge_t*) safe_realloc(eq->edges, n * sizeof(equality_graph_edge_t));
    eq->edges_capacity = n;
  }

  // Return the new element
  return &eq->edges[eq->edges_size ++];
}

/** Add the edge to the graph */
void equality_graph_add_edge(equality_graph_t* eq, equality_graph_node_id_t n1, equality_graph_node_id_t n2, equality_merge_reason_t reason) {

  // Old edges
  equality_graph_edge_id_t n1_e_id = eq->graph.data[n1];
  equality_graph_edge_id_t n2_e_id = eq->graph.data[n2];

  // Add edge n1 -> n2
  equality_graph_edge_id_t n1_new_e_id = eq->edges_size;
  equality_graph_edge_t* n1_new_e = equality_graph_new_edge(eq);
  n1_new_e->next = n1_e_id;
  n1_new_e->reason = reason;
  n1_new_e->v = n2;
  eq->graph.data[n1] = n1_new_e_id;

  // Add edge n2 -> n1
  equality_graph_edge_id_t n2_new_e_id = eq->edges_size;
  equality_graph_edge_t* n2_new_e = equality_graph_new_edge(eq);
  n2_new_e->next = n2_e_id;
  n2_new_e->reason = reason;
  n2_new_e->v = n1;
  eq->graph.data[n2] = n2_new_e_id;
}

void equality_graph_propagate(equality_graph_t* eq) {

  if (eq->in_propagate) {
    return;
  } else {
    eq->in_propagate = true;
  }

  // Propagate
  while (!merge_queue_is_empty(&eq->merge_queue) && !eq->in_conflict) {

    // Get what to merge
    const merge_data_t* merge = merge_queue_first(&eq->merge_queue);
    equality_graph_node_t* n1 = eq->nodes + merge->lhs;
    equality_graph_node_t* n2 = eq->nodes + merge->rhs;
    equality_merge_reason_t reason = merge->reason;
    merge_queue_pop(&eq->merge_queue);

    // Check if already equal
    if (n1->find == n2->find) {
      continue;
    }

    // Add the edge
    equality_graph_add_edge(eq, n1->find, n2->find, reason);

    // Swap if we prefer n2_find to be the representative
    const equality_graph_node_t* n1_find = eq->nodes + n1->find;
    const equality_graph_node_t* n2_find = eq->nodes + n2->find;
    if (equality_graph_merge_preference(n2_find, n1_find)) {
      const equality_graph_node_t* tmp = n1_find; n1_find = n2_find; n2_find = tmp;
    }

    // Merge n2 into n1
    equality_graph_merge(eq, n1->find, n2->find);
  }

  // Done, clear
  merge_queue_reset(&eq->merge_queue);
  eq->in_propagate = false;
}

void equality_graph_asssert_eq(equality_graph_t* eq,
    equality_graph_node_id_t lhs,
    equality_graph_node_id_t rhs,
    bool polarity,
    int32_t reason) {

  assert(lhs < eq->nodes_size);
  assert(rhs < eq->nodes_size);
  assert(lhs != rhs);

  if (polarity) {
    // lhs == rhs

    // Enqueue for propagation
    merge_data_t* m = merge_queue_push(&eq->merge_queue);
    m->lhs = lhs;
    m->rhs = rhs;
    m->reason = reason;

    // Propagate
    equality_graph_propagate(eq);

    return;
  } else {
    // lhs != rhs
    assert(false);
  }

}
