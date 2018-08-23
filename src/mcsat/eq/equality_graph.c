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
#include "mcsat/variable_db.h"
#include "mcsat/trail.h"

enum {
  REASON_IS_FUNCTION_DEF = -1, // f(x, y) = (f (x y))
  REASON_IS_CONSTANT_DEF = -2, // term(5) = value(5)
  REASON_IS_CONGRUENCE = -3,   // x = y -> f(x) = f(y)
  REASON_IS_TRAIL = -4         // x = v recorded in trail
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

/** Get the node given id */
static inline
eq_node_t* eq_graph_get_node(eq_graph_t* eq, eq_node_id_t id) {
  assert (id >= 0 && id < eq->nodes_size);
  return eq->nodes + id;
}

/** Get the node given id */
static inline
const eq_node_t* eq_graph_get_node_const(const eq_graph_t* eq, eq_node_id_t id) {
  assert (id >= 0 && id < eq->nodes_size);
  return eq->nodes + id;
}

void eq_graph_construct(eq_graph_t* eq, plugin_context_t* ctx, const char* name) {
  eq->ctx = ctx;

  eq->nodes_capacity = 0;
  eq->nodes_size = 0;
  eq->nodes = NULL;

  eq->edges_capacity = 0;
  eq->edges_size = 0;
  eq->edges = NULL;

  eq->uselist_nodes_capacity = 0;
  eq->uselist_nodes_size = 0;
  eq->uselist_nodes = NULL;

  eq->name = name;

  eq->in_conflict = false;
  eq->conflict_lhs = eq_node_null;
  eq->conflict_rhs = eq_node_null;

  eq->in_propagate = false;

  eq->trail_i = 0;

  init_int_hmap(&eq->kind_to_id, 0);
  init_int_hmap(&eq->term_to_id, 0);
  init_value_hmap(&eq->value_to_id, 0);
  init_pmap2(&eq->pair_to_id);

  init_ivector(&eq->kind_list, 0);
  init_ivector(&eq->terms_list, 0);
  init_value_vector(&eq->values_list, 0);
  init_ivector(&eq->pair_list, 0);

  scope_holder_construct(&eq->scope_holder);

  init_ivector(&eq->graph, 0);

  init_pmap2(&eq->pair_to_rep);

  init_merge_queue(&eq->merge_queue, 0);

  init_ivector(&eq->term_value_merges, 0);

  init_ivector(&eq->uselist, 0);
  init_ivector(&eq->uselist_updates, 0);

  // Add true/false
  eq_graph_add_value(eq, &mcsat_value_true);
  eq_graph_add_value(eq, &mcsat_value_false);

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_construct[%s]()\n", eq->name);
  }
}

void eq_graph_destruct(eq_graph_t* eq) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_destruct[%s]()\n", eq->name);
  }

  safe_free(eq->nodes);
  safe_free(eq->edges);

  delete_int_hmap(&eq->kind_to_id);
  delete_int_hmap(&eq->term_to_id);
  delete_value_hmap(&eq->value_to_id);
  delete_pmap2(&eq->pair_to_id);

  delete_ivector(&eq->kind_list);
  delete_ivector(&eq->terms_list);
  delete_value_vector(&eq->values_list);
  delete_ivector(&eq->pair_list);

  scope_holder_destruct(&eq->scope_holder);

  delete_ivector(&eq->graph);

  delete_pmap2(&eq->pair_to_rep);

  delete_merge_queue(&eq->merge_queue);

  delete_ivector(&eq->term_value_merges);

  safe_free(eq->uselist_nodes);

  delete_ivector(&eq->uselist);
  delete_ivector(&eq->uselist_updates);
}

// Default initial size and max size
#define DEFAULT_GRAPH_SIZE 10
#define MAX_GRAPH_SIZE (UINT32_MAX/sizeof(eq_node_t))

#define DEFAULT_EDGES_SIZE 10
#define MAX_EDGES_SIZE (UINT32_MAX/sizeof(eq_edge_t))

#define DEFAULT_USELIST_NODES_SIZE 10
#define MAX_USELIST_NODES_SIZE (UINT32_MAX/sizeof(eq_uselist_t))

static
eq_uselist_id_t eq_graph_new_uselist_node(eq_graph_t* eq, eq_node_id_t node, eq_uselist_id_t next) {

  uint32_t n = eq->uselist_nodes_size;
  eq_uselist_id_t id = eq->uselist_nodes_size;

  // Check if we need to resize
  if (n == eq->uselist_nodes_capacity) {
    // Compute new size
    if (n == 0) {
      n = DEFAULT_USELIST_NODES_SIZE;
    } else {
      n ++;
      n += n >> 1;
      if (n >= MAX_USELIST_NODES_SIZE) {
        out_of_memory();
      }
    }
    // Resize
    eq->uselist_nodes = (eq_uselist_t*) safe_realloc(eq->uselist_nodes, n * sizeof(eq_uselist_t));
    eq->uselist_nodes_capacity = n;
  }

  // Construct the new node
  eq_uselist_t* new_node = eq->uselist_nodes + id;
  new_node->node = node;
  new_node->next = next;

  // More nodes
  eq->uselist_nodes_size ++;

  // Return the new element
  return id;
}

static
eq_node_id_t eq_graph_new_node(eq_graph_t* eq, eq_node_type_t type, uint32_t index, bool is_constant) {

  uint32_t n = eq->nodes_size;
  eq_node_id_t id = eq->nodes_size;

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

  // Construct the new node
  eq_node_t* new_node = eq->nodes + eq->nodes_size;
  new_node->find = id;
  new_node->next = id;
  new_node->size = 1;
  new_node->type = type;
  new_node->index = index;
  new_node->is_constant = is_constant;
  new_node->uselist = eq_uselist_null;

  // More nodes
  eq->nodes_size ++;

  // Add empty edge
  ivector_push(&eq->graph, eq_edge_null);
  // Add empty uselist
  ivector_push(&eq->uselist, eq_uselist_null);

  // Return the new element
  return id;
}

static
eq_node_id_t eq_graph_add_kind(eq_graph_t* eq, term_kind_t kind) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_add_kind[%s](): %s\n", eq->name, kind_to_string(kind));
  }

  // Check if already there
  int_hmap_pair_t* find = int_hmap_get(&eq->kind_to_id, kind);
  if (find->val >= 0) {
    if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
      ctx_trace_printf(eq->ctx, "already there: %"PRIi32"\n", find->val);
    }
    return find->val;
  }

  // Index where we put the kind
  uint32_t index = eq->kind_list.size;
  ivector_push(&eq->kind_list, kind);

  // Setup the new node
  eq_node_id_t id = eq_graph_new_node(eq, EQ_NODE_KIND, index, true);
  find->val = id;

  assert(eq->nodes_size == eq->graph.size);
  assert(eq->kind_list.size + eq->terms_list.size + eq->values_list.size + eq->pair_list.size / 2 == eq->nodes_size);

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
     ctx_trace_printf(eq->ctx, "id: %"PRIi32"\n", id);
   }

  // Added, done
  return id;
}

eq_node_id_t eq_graph_add_term_internal(eq_graph_t* eq, term_t t) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_add_term[%s](): ", eq->name);
    ctx_trace_term(eq->ctx, t);
  }

  // Check if already there
  int_hmap_pair_t* find = int_hmap_get(&eq->term_to_id, t);
  if (find->val >= 0) {
    if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
      ctx_trace_printf(eq->ctx, "already there: %"PRIi32"\n", find->val);
    }
    return find->val;
  }

  // Index where we put the term
  uint32_t index = eq->terms_list.size;
  ivector_push(&eq->terms_list, t);

  // Setup the new node
  bool is_const = is_const_term(eq->ctx->terms, t);
  eq_node_id_t id = eq_graph_new_node(eq, EQ_NODE_TERM, index, is_const);
  find->val = id;

  assert(eq->nodes_size == eq->graph.size);
  assert(eq->kind_list.size + eq->terms_list.size + eq->values_list.size + eq->pair_list.size / 2 == eq->nodes_size);

  // If the node is a constant, we also create a value for it
  if (is_const) {
    mcsat_value_t t_value;
    mcsat_value_construct_from_constant_term(&t_value, eq->ctx->terms, t);
    eq_node_id_t v_id = eq_graph_add_value(eq, &t_value);
    mcsat_value_destruct(&t_value);
    merge_queue_push_init(&eq->merge_queue, id, v_id, REASON_IS_CONSTANT_DEF);
  }

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
     ctx_trace_printf(eq->ctx, "id: %"PRIi32"\n", id);
   }

  // Added, done
  return id;
}

eq_node_id_t eq_graph_add_term(eq_graph_t* eq, term_t t) {
  eq_node_id_t id = eq_graph_add_term_internal(eq, t);
  eq_graph_propagate(eq);
  return id;
}

eq_node_id_t eq_graph_add_value(eq_graph_t* eq, const mcsat_value_t* v) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_add_value[%s](): ", eq->name);
    mcsat_value_print(v, trace_out(eq->ctx->tracer));
    ctx_trace_printf(eq->ctx, "\n");
  }

  // Check if already there
  value_hmap_pair_t* find = value_hmap_get(&eq->value_to_id, v);
  if (find->val >= 0) {
    if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
      ctx_trace_printf(eq->ctx, "already there: %"PRIi32"\n", find->val);
    }
    return find->val;
  }

  // Index where we put the value
  uint32_t index = eq->values_list.size;
  mcsat_value_t* v_copy = value_vector_push(&eq->values_list);
  mcsat_value_assign(v_copy, v);

  // Setup the new node
  eq_node_id_t id = eq_graph_new_node(eq, EQ_NODE_VALUE, index, true);
  find->val = id;

  assert(eq->kind_list.size + eq->terms_list.size + eq->values_list.size + eq->pair_list.size / 2 == eq->nodes_size);
  assert(eq->nodes_size == eq->graph.size);

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "id: %"PRIi32"\n", id);
  }

  // Added, done
  return id;
}

static inline
void eq_graph_add_to_uselist(eq_graph_t* eq, eq_node_id_t n_id, eq_node_id_t parent_id) {
  assert(n_id < eq->uselist.size);
  eq_uselist_id_t n_uselist = eq->uselist.data[n_id];
  eq->uselist.data[n_id] = eq_graph_new_uselist_node(eq, parent_id, n_uselist);
  ivector_push(&eq->uselist_updates, n_id);
}

eq_node_id_t eq_graph_add_pair(eq_graph_t* eq, eq_node_id_t p1, eq_node_id_t p2) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_add_pair[%s]()\n", eq->name);
  }

  // Check if already there
  pmap2_rec_t* find = pmap2_get(&eq->pair_to_id, p1, p2);
  if (find->val >= 0) {
    if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
      ctx_trace_printf(eq->ctx, "already there: %"PRIi32"\n", find->val);
    }
    return find->val;
  }

  // Index where we put the value
  uint32_t index = eq->pair_list.size;
  ivector_push(&eq->pair_list, p1);
  ivector_push(&eq->pair_list, p2);

  // Setup the new node
  eq_node_t* p1_node = eq_graph_get_node(eq, p1);
  eq_node_t* p2_node = eq_graph_get_node(eq, p2);
  bool is_constant = p1_node->is_constant && p2_node->is_constant;
  eq_node_id_t id = eq_graph_new_node(eq, EQ_NODE_PAIR, index, is_constant);
  find->val = id;

  assert(eq->kind_list.size + eq->terms_list.size + eq->values_list.size + eq->pair_list.size / 2 == eq->nodes_size);
  assert(eq->nodes_size == eq->graph.size);

  // Add to uselists: p1 is used in id, p2 is used in id
  eq_graph_add_to_uselist(eq, p1, id);
  eq_graph_add_to_uselist(eq, p2, id);

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "id: %"PRIi32"\n", id);
  }

  // Added, done
  return id;
}

void eq_graph_update_pair_hash(eq_graph_t* eq, eq_node_id_t pair_id) {
  // n = (n1, n2)
  const eq_node_t* n = eq_graph_get_node_const(eq, pair_id);
  assert(n->type == EQ_NODE_PAIR);
  // n1
  eq_node_id_t p1 = eq->pair_list.data[n->index];
  const eq_node_t* n1 = eq_graph_get_node_const(eq, p1);
  // n2
  eq_node_id_t p2 = eq->pair_list.data[n->index + 1];
  const eq_node_t* n2 = eq_graph_get_node_const(eq, p2);

  // Store normalized pair or merge if someone is already there
  pmap2_rec_t* find = pmap2_get(&eq->pair_to_rep, n1->find, n2->find);
  if (find->val < 0) {
    // New representative
    find->val = pair_id;
  } else {
    // Merge with existing representative
    if (find->val != pair_id) {
      merge_queue_push_init(&eq->merge_queue, pair_id, find->val, REASON_IS_CONGRUENCE);
    }
  }
}

eq_node_id_t eq_graph_add_ufun_term(eq_graph_t* eq, term_t t, term_t f, uint32_t n, const term_t* c) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_ufun_term[%s](): ", eq->name);
    ctx_trace_term(eq->ctx, t);
  }

  assert(n >= 1);
  assert(!eq_graph_has_term(eq, t));

  // Add the term f
  eq_node_id_t f_id = eq_graph_add_term_internal(eq, t);

  // We add the function term f(x_1, ..., x_n) as a sequence of pair nodes:
  //
  //   n_1 = (x_n-1, x_n)
  //   n_2 = (x_n-2, n_1)
  //      ...
  //   n_n = (f, n_n-1)
  //
  // These nodes we do congruence over.

  // Add the pairs for children
  int32_t i = n-1;
  eq_node_id_t p2 = eq_graph_add_term_internal(eq, c[i]);
  for (-- i; i >= 0; -- i) {
    eq_node_id_t p1 = eq_graph_add_term_internal(eq, c[i]);
    // Add the graph node (p1, p2)
    p2 = eq_graph_add_pair(eq, p1, p2);
    // Store in the hash table
    eq_graph_update_pair_hash(eq, p2);
  }

  // Add the final function application
  eq_node_id_t p1 = eq_graph_add_term_internal(eq, f);
  // Add the graph node (p1, p2)
  p2 = eq_graph_add_pair(eq, p1, p2);
  // Store in the hash table
  eq_graph_update_pair_hash(eq, p2);

  // Add the equality f = p2
  merge_queue_push_init(&eq->merge_queue, f_id, p2, REASON_IS_FUNCTION_DEF);

  // We added lots of stuff, maybe there were merges
  eq_graph_propagate(eq);

  return p2;
}

eq_node_id_t eq_graph_add_ifun_term(eq_graph_t* eq, term_t t, term_kind_t f, uint32_t n, const term_t* c) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_ifun_term[%s](): ", eq->name);
    ctx_trace_term(eq->ctx, t);
  }

  assert(n >= 1);
  assert(!eq_graph_has_term(eq, t));

  // Add the term f
  eq_node_id_t f_id = eq_graph_add_term_internal(eq, t);

  // We add the function term f(x_1, ..., x_n) as a sequence of pair nodes:
  //
  //   n_1 = (x_n-1, x_n)
  //   n_2 = (x_n-2, n_1)
  //      ...
  //   n_n = (f, n_n-1)
  //
  // These nodes we do congruence over.

  // Add the pairs for children
  int32_t i = n-1;
  eq_node_id_t p2 = eq_graph_add_term_internal(eq, c[i]);
  for (-- i; i >= 0; -- i) {
    eq_node_id_t p1 = eq_graph_add_term_internal(eq, c[i]);
    // Add the graph node (p1, p2)
    p2 = eq_graph_add_pair(eq, p1, p2);
    // Store in the hash table
    eq_graph_update_pair_hash(eq, p2);
  }

  // Add the final function application
  eq_node_id_t p1 = eq_graph_add_kind(eq, f);
  // Add the graph node (p1, p2)
  p2 = eq_graph_add_pair(eq, p1, p2);
  // Store in the hash table
  eq_graph_update_pair_hash(eq, p2);

  // Add the equality f = p2
  merge_queue_push_init(&eq->merge_queue, f_id, p2, REASON_IS_FUNCTION_DEF);

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

bool eq_graph_has_term(const eq_graph_t* eq, term_t t) {
  return int_hmap_find((int_hmap_t*) &eq->term_to_id, t) != NULL;
}

bool eq_graph_has_value(const eq_graph_t* eq, const mcsat_value_t* v) {
  return value_hmap_find(&eq->value_to_id, v) != NULL;
}

void eq_graph_print_node(const eq_graph_t* eq, const eq_node_t* n, FILE* out, bool print_id) {
  eq_node_id_t n_id = eq_graph_get_node_id(eq, n);
  switch (n->type) {
  case EQ_NODE_KIND: {
    term_kind_t kind = eq->kind_list.data[n->index];
    fprintf(out, "%s", kind_to_string(kind));
    if (print_id) {
      fprintf(out, "(id=%"PRIu32", idx=%"PRIu32")", n_id, n->index);
    }
    break;
  }
  case EQ_NODE_TERM: {
    term_t t = eq->terms_list.data[n->index];
    term_print_to_file(out, eq->ctx->terms, t);
    if (print_id) {
      fprintf(out, " (id=%"PRIu32", idx=%"PRIu32")", n_id, n->index);
    }
    break;
  }
  case EQ_NODE_VALUE: {
    const mcsat_value_t* v = eq->values_list.data + n->index;
    mcsat_value_print(v, out);
    if (print_id) {
      fprintf(out, " (id=%"PRIu32", idx=%"PRIu32")", n_id, n->index);
    }
    break;
  }
  case EQ_NODE_PAIR: {
    fprintf(out, "[");
    eq_node_id_t p1 = eq->pair_list.data[n->index];
    eq_graph_print_node(eq, eq_graph_get_node_const(eq, p1), out, false);
    fprintf(out, ", ");
    eq_node_id_t p2 = eq->pair_list.data[n->index + 1];
    eq_graph_print_node(eq, eq_graph_get_node_const(eq, p2), out, false);
    fprintf(out, "]");
    if (print_id) {
      fprintf(out, " (id=%"PRIu32", idx=%"PRIu32")", n_id, n->index);
    }
    break;
  }
  }
}

void eq_graph_print_class(const eq_graph_t* eq, eq_node_id_t start_node_id, FILE* out) {
  const eq_node_t* n = eq_graph_get_node_const(eq, start_node_id);
  eq_node_id_t n_id = start_node_id;
  bool first = true;
  do {
    if (!first) { fprintf(out, ", "); }
    eq_graph_print_node(eq, n, out, true);
    n = eq->nodes + n->next;
    n_id = eq_graph_get_node_id(eq, n);
    first = false;
  } while (n_id != start_node_id);
}

void eq_graph_print(const eq_graph_t* eq, FILE* out) {
  uint32_t i;

  fprintf(out, "eq_graph[%s]:\n", eq->name);
  fprintf(out, "nodes:\n");

  for (i = 0; i < eq->nodes_size; ++ i) {
    const eq_node_t* n = eq_graph_get_node_const(eq, i);
    fprintf(out, "  ");
    eq_graph_print_node(eq, n, out, true);
    fprintf(out, ": ");
    eq_graph_print_class(eq, n->find, out);
    fprintf(out, "\n");
  }
}

/** Merge node n2 into n1 */
static
void eq_graph_merge(eq_graph_t* eq, eq_node_id_t n1_id, eq_node_id_t n2_id) {

  eq_node_t* n1 = eq->nodes + n1_id;
  eq_node_t* n2 = eq->nodes + n2_id;

  assert(n1->find == n1_id);
  assert(n2->find == n2_id);
  assert(n1_id != n2_id);

  // Update the find in n2's class
  do {
    n2->find = n1_id;
    n2 = eq->nodes + n2->next;
  } while (n2->find != n1_id);

  // Finally merge the lists (circular lists)
  eq_node_id_t tmp = n1->next;
  n1->next = n2->next;
  n2->next = tmp;

  // Update the size
  n1->size += n2->size;
}

/** Un-merge node n2 from n1 */
static
void eq_graph_unmerge(eq_graph_t* eq, eq_node_id_t n1_id, eq_node_id_t n2_id) {

  eq_node_t* n1 = eq->nodes + n1_id;
  eq_node_t* n2 = eq->nodes + n2_id;

  assert(n1->find == n1_id);
  assert(n2->find == n1_id);
  assert(n1_id != n2_id);

  // Update the size
  assert(n1->size > n2->size);
  n1->size -= n2->size;

  // Unmerge the lists (circular lists)
  eq_node_id_t tmp = n1->next;
  n1->next = n2->next;
  n2->next = tmp;

  // Update the find in n2's class
  do {
    n2->find = n2_id;
    n2 = eq->nodes + n2->next;
  } while (n2->find != n2_id);
}


/** Do we prefer n1 to n2 */
static inline
bool eq_graph_merge_preference(const eq_node_t* n1, const eq_node_t* n2) {

  // If n1 is a value node, then yes
  if (n1->type == EQ_NODE_VALUE) {
    return true;
  }

  // If n1 is a constant then yes
  if (n1->is_constant) {
    return true;
  }

  // Otherwise we prefer a biger one (so that we update less nodes)
  return n1->size < n2->size;
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
  n1_new_e->u = n1;
  n1_new_e->v = n2;
  eq->graph.data[n1] = n1_new_e_id;

  // Add edge n2 -> n1
  eq_edge_id_t n2_new_e_id = eq->edges_size;
  eq_edge_t* n2_new_e = eq_graph_new_edge(eq);
  n2_new_e->next = n2_e_id;
  n2_new_e->reason = reason;
  n2_new_e->u = n2;
  n2_new_e->v = n1;
  eq->graph.data[n2] = n2_new_e_id;
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
    const eq_node_t* n1 = eq_graph_get_node_const(eq, merge->lhs);
    const eq_node_t* n2 = eq_graph_get_node_const(eq, merge->rhs);
    eq_reason_t reason = merge->reason;
    merge_queue_pop(&eq->merge_queue);

    // Check if already equal
    if (n1->find == n2->find) {
      continue;
    }

    // Add the edge
    eq_graph_add_edge(eq, n1->find, n2->find, reason);

    // Swap if we prefer n2_find to be the representative
    const eq_node_t* n1_find = eq_graph_get_node_const(eq, n1->find);
    const eq_node_t* n2_find = eq_graph_get_node_const(eq, n2->find);
    if (eq_graph_merge_preference(n2_find, n1_find)) {
      const eq_node_t* tmp = n1_find; n1_find = n2_find; n2_find = tmp;
    }

    bool n1_is_const = n1_find->is_constant;
    bool n2_is_const = n2_find->is_constant;

    // If we merge two same-type nodes that are constant we have a conflict
    if (n1_is_const && n2_is_const && n1->type == n2->type) {
      eq->in_conflict = true;
      eq->conflict_lhs = n1->find;
      eq->conflict_rhs = n2->find;
    }
    // If we merge into a value we remember all the terms
    else if (n1->type == EQ_NODE_VALUE) {
      // Add n2 term nodes to notification list
      const eq_node_t* it = n2_find;
      do {
        if (it->type == EQ_NODE_TERM) {
          ivector_push(&eq->term_value_merges, eq_graph_get_node_id(eq, it));
        }
        it = eq_graph_get_node(eq, it->next);
      } while (it != n2_find);
    }

    // Merge n2 into n1
    eq_graph_merge(eq, n1->find, n2->find);
  }

  // Done, clear
  merge_queue_reset(&eq->merge_queue);
  eq->in_propagate = false;
}

void eq_graph_assert_eq(eq_graph_t* eq, eq_node_id_t lhs, eq_node_id_t rhs,
    bool polarity, int32_t reason) {

  assert(lhs < eq->nodes_size);
  assert(rhs < eq->nodes_size);
  assert(lhs != rhs);

  if (polarity) {
    // lhs == rhs

    // Enqueue for propagation
    merge_queue_push_init(&eq->merge_queue, lhs, rhs, reason);

    // Propagate
    eq_graph_propagate(eq);

    return;
  } else {
    // lhs != rhs
    assert(false);
  }

}

void eq_graph_get_propagated_terms(eq_graph_t* eq, ivector_t* out_terms) {
  // Copy over the terms that are equal to a value
  uint32_t i;
  for (i = 0; i < eq->term_value_merges.size; ++ i) {
    eq_node_id_t n_id = eq->term_value_merges.data[i];
    const eq_node_t* n = eq_graph_get_node(eq, n_id);
    eq_node_id_t n_find_id = n->find;
    const eq_node_t* n_find = eq_graph_get_node(eq, n_find_id);
    if (n->type == EQ_NODE_TERM && n_find->type == EQ_NODE_VALUE) {
      ivector_push(out_terms, eq->terms_list.data[n->index]);
    }
  }
  // Clear the vector
  ivector_reset(&eq->term_value_merges);
}

const mcsat_value_t* eq_graph_get_propagated_term_value(const eq_graph_t* eq, term_t t) {
  assert(eq_graph_has_term(eq, t));
  eq_node_id_t t_id = eq_graph_term_id(eq, t);
  const eq_node_t* n = eq_graph_get_node_const(eq, t_id);
  eq_node_id_t n_find_id = n->find;
  const eq_node_t* n_find = eq_graph_get_node_const(eq, n_find_id);
  assert(n_find->type == EQ_NODE_VALUE);
  return eq->values_list.data + n_find->index;
}

void eq_graph_propagate_trail(eq_graph_t* eq) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_propagate_trail[%s]()\n", eq->name);
  }

  const mcsat_trail_t* trail = eq->ctx->trail;
  variable_db_t* var_db = eq->ctx->var_db;

  for (; eq->trail_i < trail_size(trail); ++ eq->trail_i) {
    variable_t x = trail_at(trail, eq->trail_i);
    term_t x_term = variable_db_get_term(var_db, x);
    if (eq_graph_has_term(eq, x_term)) {
      const mcsat_value_t* v = trail_get_value(trail, x);
      eq_node_id_t v_id = eq_graph_add_value(eq, v);
      eq_node_id_t x_id = eq_graph_term_id(eq, x_term);
      eq_graph_assert_eq(eq, v_id, x_id, true, REASON_IS_TRAIL);
    }
  }
}

void eq_graph_push(eq_graph_t* eq) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::detail")) {
    ctx_trace_printf(eq->ctx, "eq_graph_push[%s]()\n", eq->name);
    eq_graph_print(eq, ctx_trace_out(eq->ctx));
  }

  scope_holder_push(&eq->scope_holder,
      &eq->kind_list.size,
      &eq->terms_list.size,
      &eq->values_list.size,
      &eq->pair_list.size,
      &eq->nodes_size,
      &eq->edges_size,
      &eq->graph.size,
      &eq->trail_i,
      &eq->uselist_nodes_size,
      &eq->uselist.size,
      &eq->uselist_updates.size,
      NULL
  );

  // Push the pair maps
  pmap2_push(&eq->pair_to_id);
  pmap2_push(&eq->pair_to_rep);

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_propagate_trail[%s]()\n", eq->name);
  }

  assert(merge_queue_is_empty(&eq->merge_queue));
}

void eq_graph_pop(eq_graph_t* eq) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::detail")) {
    ctx_trace_printf(eq->ctx, "eq_graph_pop[%s](): before\n", eq->name);
    eq_graph_print(eq, ctx_trace_out(eq->ctx));
  }

  uint32_t kind_list_size;
  uint32_t term_list_size;
  uint32_t value_list_size;
  uint32_t pair_list_size;
  uint32_t nodes_size;
  uint32_t edges_size;
  uint32_t graph_size;
  uint32_t uselist_nodes_size;
  uint32_t uselist_size;
  uint32_t uselist_updates_size;

  scope_holder_pop(&eq->scope_holder,
      &kind_list_size,
      &term_list_size,
      &value_list_size,
      &pair_list_size,
      &nodes_size,
      &edges_size,
      &graph_size,
      &eq->trail_i,
      &uselist_nodes_size,
      &uselist_size,
      &uselist_updates_size,
      NULL
  );

  uint32_t i;

  // Remove any added edges
  const eq_edge_t* edge = eq->edges + eq->edges_size;
  while (eq->edges_size > edges_size) {
    // Remove edge: point to the previous edge in list
    edge = edge - 2;
    eq->graph.data[edge->u] = edge->next;
    eq->edges_size -= 2;

    // Un-merge the two nodes
    eq_graph_unmerge(eq, edge->u, edge->v);
  }

  // Remove added kinds
  for (i = kind_list_size; i < eq->kind_list.size; ++ i) {
    term_kind_t kind = eq->kind_list.data[i];
    int_hmap_pair_t* find = int_hmap_find(&eq->kind_to_id, kind);
    int_hmap_erase(&eq->kind_to_id, find);
  }
  ivector_shrink(&eq->kind_list, kind_list_size);

  // Remove added terms
  for (i = term_list_size; i < eq->terms_list.size; ++ i) {
    term_t t = eq->terms_list.data[i];
    int_hmap_pair_t* find = int_hmap_find(&eq->term_to_id, t);
    int_hmap_erase(&eq->term_to_id, find);
  }
  ivector_shrink(&eq->terms_list, term_list_size);

  // Remove added values
  for (i = value_list_size; i < eq->values_list.size; ++ i) {
    const mcsat_value_t* v = eq->values_list.data + i;
    value_hmap_pair_t* find = value_hmap_find(&eq->value_to_id, v);
    value_hmap_erase(&eq->value_to_id, find);
  }
  value_vector_shrink(&eq->values_list, value_list_size);

  // Remove added pairs (map pops automatically, see below)
  ivector_shrink(&eq->pair_list, pair_list_size);

  // Revert the uselist updates
  while (eq->uselist_updates.size > uselist_updates_size) {
    eq_node_id_t n_id = ivector_pop2(&eq->uselist_updates);
    assert(n_id < eq->uselist.size);
    eq_uselist_id_t n_uselist_id = eq->uselist.data[n_id];
    assert(n_uselist_id < eq->uselist_nodes_size);
    const eq_uselist_t* n_uselist = eq->uselist_nodes + n_uselist_id;
    eq->uselist.data[n_id] = n_uselist->next;
  }
  eq->uselist_nodes_size = uselist_nodes_size;
  ivector_shrink(&eq->uselist, uselist_size);

  // Remove the added nodes
  eq->nodes_size = nodes_size;

  // Pop the graph size
  ivector_shrink(&eq->graph, graph_size);

  // Pop the pair maps
  pmap2_pop(&eq->pair_to_id);
  pmap2_pop(&eq->pair_to_rep);

  // Reset the merge queue
  merge_queue_reset(&eq->merge_queue);

  // Clear conflict
  eq->in_conflict = false;
  eq->conflict_lhs = eq_node_null;
  eq->conflict_rhs = eq_node_null;

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::detail")) {
    ctx_trace_printf(eq->ctx, "eq_graph_pop[%s](): after\n", eq->name);
    eq_graph_print(eq, ctx_trace_out(eq->ctx));
  }

}
