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

enum {
  REASON_IS_FUNCTION_DEF = -1, // f(x, y) = (f (x y))
  REASON_IS_GRAPH_CONGRUENCE = -2    // x = y -> f(x) = f(y)
};

#include <inttypes.h>
#include <assert.h>

static
void eq_graph_propagate(eq_graph_t* eq);

/** Get the id of the node */
static inline
eq_node_id_t eq_graph_get_node_id(const eq_graph_t* eq, const eq_node_t* n) {
  return n - eq->nodes;
}

void eq_graph_construct(eq_graph_t* eq, plugin_context_t* ctx, const char* name) {
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
  init_pmap2(&eq->pair_to_rep);

  scope_holder_construct(&eq->scope_holder);

  // Add true/false
  eq_graph_add_value(eq, &mcsat_value_true);
  eq_graph_add_value(eq, &mcsat_value_false);
}

void eq_graph_destruct(eq_graph_t* eq) {
  safe_free(eq->nodes);
  safe_free(eq->edges);

  delete_int_hmap(&eq->term_to_id);
  delete_value_hmap(&eq->value_to_id);
  delete_ivector(&eq->terms_list);
  delete_value_vector(&eq->values_list);
  delete_merge_queue(&eq->merge_queue);
  delete_ivector(&eq->graph);
  delete_pmap2(&eq->pair_to_rep);
}

// Default initial size and max size
#define DEFAULT_GRAPH_SIZE 10
#define MAX_GRAPH_SIZE (UINT32_MAX/sizeof(eq_node_t))

#define DEFAULT_EDGES_SIZE 10
#define MAX_EDGES_SIZE (UINT32_MAX/sizeof(eq_edge_t))

static
eq_node_t* eq_graph_new_node(eq_graph_t* eq) {
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
    eq->nodes = (eq_node_t*) safe_realloc(eq->nodes, n * sizeof(eq_node_t));
    eq->nodes_capacity = n;
  }

  // Return the new element
  return &eq->nodes[eq->nodes_size ++];
}

eq_node_id_t eq_graph_add_term(eq_graph_t* eq, term_t t) {

  // New id of the node
  eq_node_id_t id = eq->nodes_size;
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
  eq_node_t* node = eq_graph_new_node(eq);
  node->type = EQ_NODE_TERM;
  node->find = id;
  node->next = id;
  node->index = index;
  node->is_constant = is_const_term(eq->ctx->terms, t);

  // No edges
  ivector_push(&eq->graph, eq_edge_null);

  assert(eq->nodes_size == eq->graph.size);
  assert(eq->terms_list.size + eq->values_list.size + eq->pairs_list.size / 2 == eq->nodes_size);

  // Added, done
  return id;
}

eq_node_id_t eq_graph_add_value(eq_graph_t* eq, const mcsat_value_t* v) {

  // New id of the node
  eq_node_id_t id = eq->nodes_size;
  uint32_t index = eq->values_list.size;

  // Check if already there
  value_hmap_pair_t* find = value_hmap_get(&eq->value_to_id, v);
  if (find->val < 0) {
    find->val = id;
    mcsat_value_t* v_copy = value_vector_push(&eq->values_list);
    mcsat_value_assign(v_copy, v);
  } else {
    return find->val;
  }

  // Setup the new node
  eq_node_t* node = eq_graph_new_node(eq);
  node->type = EQ_NODE_VALUE;
  node->find = id;
  node->next = id;
  node->index = index;
  node->is_constant = true;

  // No edges
  ivector_push(&eq->graph, eq_edge_null);

  assert(eq->terms_list.size + eq->values_list.size == eq->nodes_size);
  assert(eq->nodes_size == eq->graph.size);

  // Added, done
  return id;
}

eq_node_id_t eq_graph_add_pair(eq_graph_t* eq,
    eq_node_id_t p1,
    eq_node_id_t p2) {

  // New id of the node
  eq_node_id_t id = eq->nodes_size;
  uint32_t index = eq->pairs_list.size;

  // Check if already there
  pmap2_rec_t* find = pmap2_get(&eq->pair_to_id, p1, p2);
  if (find->val < 0) {
    find->val = id;
    ivector_push(&eq->pairs_list, p1);
    ivector_push(&eq->pairs_list, p2);
  } else {
    return find->val;
  }

  // Setup the new node
  eq_node_t* node = eq_graph_new_node(eq);
  node->type = EQ_NODE_PAIR;
  node->find = id;
  node->next = id;
  node->index = index;
  node->is_constant = eq->nodes[p1].is_constant && eq->nodes[p2].is_constant;

  // No edges
  ivector_push(&eq->graph, eq_edge_null);

  assert(eq->terms_list.size + eq->values_list.size == eq->nodes_size);
  assert(eq->nodes_size == eq->graph.size);

  // Add to use-lists
  assert(false);

  // Added, done
  return id;
}

void eq_graph_update_pair_hash(eq_graph_t* eq, eq_node_id_t pair_id) {
  // n = (n1, n2)
  const eq_node_t* n = eq->nodes + pair_id;
  assert(n->type == EQ_NODE_PAIR);
  // n1
  eq_node_id_t p1 = eq->pairs_list.data[n->index];
  const eq_node_t* n1 = eq->nodes + p1;
  // n2
  eq_node_id_t p2 = eq->pairs_list.data[n->index + 1];
  const eq_node_t* n2 = eq->nodes + p2;

  // Store normalized pair or merge if someone is already there
  pmap2_rec_t* find = pmap2_get(&eq->pair_to_rep, n1->find, n2->find);
  if (find->val < 0) {
    // New representative
    find->val = pair_id;
  } else {
    // Merge with existing representative
    if (find->val != pair_id) {
      merge_data_t* new_merge = merge_queue_push(&eq->merge_queue);
      new_merge->lhs = pair_id;
      new_merge->rhs = find->val;
      new_merge->reason = REASON_IS_GRAPH_CONGRUENCE;
    }
  }
}

eq_node_id_t eq_graph_add_fun_term(eq_graph_t* eq,
    term_t f, uint32_t n_subterms, const term_t* subterms) {

  assert(n_subterms >= 2);
  assert(!eq_graph_has_term(eq, f));

  // Add the term f
  eq_node_id_t f_id = eq_graph_add_term(eq, f);

  // We add the function term f(x_1, ..., x_n) as a sequence of pair nodes:
  //
  //   n_1 = (x_n-1, x_n)
  //   n_2 = (x_n-2, n_1)
  //      ...
  //   n_n = (f, n_n-1)
  //
  // These nodes we do congruence over.

  // Add the pairs
  int32_t i = n_subterms-1;
  eq_node_id_t p2 = eq_graph_add_term(eq, subterms[i]);
  for (-- i; i >= 0; -- i) {
    eq_node_id_t p1 = eq_graph_add_term(eq, subterms[i]);
    // Add the graph node (p1, p2)
    p2 = eq_graph_add_pair(eq, p1, p2);
    // Store in the hash table
    eq_graph_update_pair_hash(eq, p2);
  }

  // Add the equality f = p2
  merge_data_t* new_merge = merge_queue_push(&eq->merge_queue);
  new_merge->lhs = f_id;
  new_merge->rhs = p2;
  new_merge->reason = REASON_IS_FUNCTION_DEF;

  // We added lots of stuff, maybe there were merges
  eq_graph_propagate(eq);

  return p2;
}

eq_node_id_t eq_graph_term_id(const eq_graph_t* eq, term_t t) {
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &eq->term_to_id, t);
  assert(find != NULL);
  return find->val;
}

eq_node_id_t eq_graph_value_id(const eq_graph_t* eq, const mcsat_value_t* v) {
  value_hmap_pair_t* find = value_hmap_find(&eq->value_to_id, v);
  assert(find != NULL);
  return find->val;
}

bool eq_graph_has_term(const eq_graph_t* eq, variable_t t) {
  return int_hmap_find((int_hmap_t*) &eq->term_to_id, t) != NULL;
}

bool eq_graph_has_value(const eq_graph_t* eq, const mcsat_value_t* v) {
  return value_hmap_find(&eq->value_to_id, v) != NULL;
}

void eq_graph_push(eq_graph_t* eq) {
  scope_holder_push(&eq->scope_holder,
      &eq->terms_list.size,
      &eq->values_list.size,
      NULL
  );
}

void eq_graph_pop(eq_graph_t* eq) {
  uint32_t term_list_size, value_list_size;

  scope_holder_pop(&eq->scope_holder,
      &term_list_size,
      &value_list_size,
      NULL
  );

  // TODO: actually remove data
  assert(false);
}

void eq_graph_print_class(const eq_graph_t* eq, eq_node_id_t start_node_id, FILE* out) {
  const eq_node_t* n = eq->nodes + start_node_id;
  eq_node_id_t n_id = eq_graph_get_node_id(eq, n);
  bool first = true;
  do {
    if (!first) { fprintf(out, ", "); }
    switch (n->type) {
    case EQ_NODE_TERM: {
      const mcsat_value_t* v = eq->values_list.data + n->index;
      mcsat_value_print(v, out);
      fprintf(out, "(id=%"PRIu32", idx=%"PRIu32")", n->index, n_id);
      break;
    }
    case EQ_NODE_VALUE: {
      term_t t = eq->terms_list.data[n->index];
      term_print_to_file(out, eq->ctx->terms, t);
      fprintf(out, "(id=%"PRIu32", idx=%"PRIu32")", n->index, n_id);
      break;
    }
    case EQ_NODE_PAIR: {
      fprintf(out, "(id=%"PRIu32", idx=%"PRIu32")", n->index, n_id);
      break;
    }
    }
    n = eq->nodes + n->next;
    first = false;
  } while (n->index != start_node_id);
}

void eq_graph_print(const eq_graph_t* eq, FILE* out) {
  uint32_t i;

  // Print all the terms
  for (i = 0; i < eq->terms_list.size; ++ i) {
    term_t t = eq->terms_list.data[i];
    term_print_to_file(out, eq->ctx->terms, t);
    fprintf(out, " (%"PRIu32"): ", i);
    eq_node_id_t t_id = eq_graph_term_id(eq, t);
    eq_graph_print_class(eq, t_id, out);
    fprintf(out, "\n");
  }

  // Print all the values
  for (i = 0; i < eq->values_list.size; ++ i) {
    const mcsat_value_t* v = eq->values_list.data + i;
    mcsat_value_print(v, out);
    fprintf(out, " (%"PRIu32"): ", i);
    uint32_t v_id = eq_graph_value_id(eq, v);
    eq_graph_print_class(eq, v_id, out);
    fprintf(out, "\n");
  }
}

/** Merge node n2 into n1 */
static
void eq_graph_merge(eq_graph_t* eq, eq_node_id_t n1_id, eq_node_id_t n2_id) {

  eq_node_t* n1 = eq->nodes + n1_id;
  eq_node_t* n2 = eq->nodes + n2_id;

  assert(n1->find == n1_id);
  assert(n1->find == n2_id);
  assert(n1_id != n2_id);

  // Update the find in n2's class
  do {
    n2->find = n1->find;
    n2 = eq->nodes + n2->next;
  } while (n2->find != n1->find);

  // Finally merge the lists (circular lists)
  eq_node_id_t tmp = n1->next;
  n1->next = n2->next;
  n2->next = tmp;

}

/** Do we prefer n1 to n2 */
static inline
bool eq_graph_merge_preference(const eq_node_t* n1, const eq_node_t* n2) {

  // If n1 is a constant then yes
  if (n1->is_constant) {
    return true;
  }

  // Otherwise we don't prefer n1 (we don't care)
  return false;
}

/** Allocate a new edge */
static
eq_edge_t* eq_graph_new_edge(eq_graph_t* eq) {
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
    eq->edges = (eq_edge_t*) safe_realloc(eq->edges, n * sizeof(eq_edge_t));
    eq->edges_capacity = n;
  }

  // Return the new element
  return &eq->edges[eq->edges_size ++];
}

/** Add the edge to the graph */
void eq_graph_add_edge(eq_graph_t* eq, eq_node_id_t n1, eq_node_id_t n2, eq_reason_t reason) {

  // Old edges
  eq_edge_id_t n1_e_id = eq->graph.data[n1];
  eq_edge_id_t n2_e_id = eq->graph.data[n2];

  // Add edge n1 -> n2
  eq_edge_id_t n1_new_e_id = eq->edges_size;
  eq_edge_t* n1_new_e = eq_graph_new_edge(eq);
  n1_new_e->next = n1_e_id;
  n1_new_e->reason = reason;
  n1_new_e->v = n2;
  eq->graph.data[n1] = n1_new_e_id;

  // Add edge n2 -> n1
  eq_edge_id_t n2_new_e_id = eq->edges_size;
  eq_edge_t* n2_new_e = eq_graph_new_edge(eq);
  n2_new_e->next = n2_e_id;
  n2_new_e->reason = reason;
  n2_new_e->v = n1;
  eq->graph.data[n2] = n2_new_e_id;
}

static
bool eq_graph_evaluate_eq(const eq_graph_t* eq, eq_node_id_t n1,eq_node_id_t n2) {
  return true;
}

static
void eq_graph_propagate(eq_graph_t* eq) {

  if (eq->in_propagate) {
    return;
  } else {
    eq->in_propagate = true;
  }

  // Propagate
  while (!merge_queue_is_empty(&eq->merge_queue) && !eq->in_conflict) {

    // Get what to merge
    const merge_data_t* merge = merge_queue_first(&eq->merge_queue);
    eq_node_t* n1 = eq->nodes + merge->lhs;
    eq_node_t* n2 = eq->nodes + merge->rhs;
    eq_reason_t reason = merge->reason;
    merge_queue_pop(&eq->merge_queue);

    // Check if already equal
    if (n1->find == n2->find) {
      continue;
    }

    // Add the edge
    eq_graph_add_edge(eq, n1->find, n2->find, reason);

    // Swap if we prefer n2_find to be the representative
    const eq_node_t* n1_find = eq->nodes + n1->find;
    const eq_node_t* n2_find = eq->nodes + n2->find;
    if (eq_graph_merge_preference(n2_find, n1_find)) {
      const eq_node_t* tmp = n1_find; n1_find = n2_find; n2_find = tmp;
    }

    bool n1_is_const = n1_find->is_constant;
    bool n2_is_const = n2_find->is_constant;

    // If we merge two nodes that are constant we might have a conflict
    if (n1_is_const && n2_is_const) {
      if (!eq_graph_evaluate_eq(eq, n1->find, n2->find)) {
        eq->in_conflict = true;
        eq->conflict_lhs = n1->find;
        eq->conflict_rhs = n2->find;
      }
    }

    if (n1_is_const && !n2_is_const) {
      // Add n2 term nodes to notification list
      const eq_node_t* it = n2_find;
      do {
        ivector_push(&eq->constant_merges, eq_graph_get_node_id(eq, it));
        it = eq->nodes + it->next;
      } while (it != n2_find);
    }

    // Merge n2 into n1
    eq_graph_merge(eq, n1->find, n2->find);
  }

  // Done, clear
  merge_queue_reset(&eq->merge_queue);
  eq->in_propagate = false;
}

void eq_graph_assert_eq(eq_graph_t* eq,
    eq_node_id_t lhs,
    eq_node_id_t rhs,
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
    eq_graph_propagate(eq);

    return;
  } else {
    // lhs != rhs
    assert(false);
  }

}
