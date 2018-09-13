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

#include <inttypes.h>
#include <assert.h>

static
void eq_graph_propagate(eq_graph_t* eq);

static inline
const char* eq_graph_reason_to_string(eq_reason_type_t reason) {
  switch (reason) {
  case REASON_IS_FUNCTION_DEF: return "function definition";
  case REASON_IS_CONSTANT_DEF: return "constant definition";
  case REASON_IS_CONGRUENCE: return "congruence";
  case REASON_IS_CONGRUENCE_EQ_SYM: return "eq sym congruence";
  case REASON_IS_TRUE_EQUALITY: return "equality = true";
  case REASON_IS_REFLEXIVITY: return "reflexivity";
  case REASON_IS_EVALUATION: return "eq evaluation";
  case REASON_IS_IN_TRAIL: return "assigned in trail";
  case REASON_IS_USER: return "user asserted";
  default:
    assert(false);
  }
  return "unknown";
}

static inline
const char* eq_graph_reason_to_short_string(eq_reason_type_t reason) {
  switch (reason) {
  case REASON_IS_FUNCTION_DEF: return "f-def";
  case REASON_IS_CONSTANT_DEF: return "c-def";
  case REASON_IS_CONGRUENCE: return "cc";
  case REASON_IS_CONGRUENCE_EQ_SYM: return "e-cc";
  case REASON_IS_TRUE_EQUALITY: return "eq";
  case REASON_IS_REFLEXIVITY: return "refl";
  case REASON_IS_EVALUATION: return "eval";
  case REASON_IS_IN_TRAIL: return "trail";
  case REASON_IS_USER: return "user";
  default:
    assert(false);
  }
  return "unknown";
}

static
void eq_graph_eq_assigned_to_value(eq_graph_t* eq, eq_node_id_t eq_id, eq_node_id_t v_id);

static
void eq_graph_eq_args_updated(eq_graph_t* eq, eq_node_id_t eq_id);

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
  assert (id < eq->nodes_size);
  return eq->nodes + id;
}

static inline
const eq_node_id_t* eq_graph_get_children(const eq_graph_t* eq, eq_node_id_t id) {
  assert (id < eq->nodes_size);
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &eq->node_to_children, id);
  if (find != NULL) {
    return (const eq_node_id_t*) eq->children_list.data + find->val;
  } else {
    return NULL;
  }
}

static inline
bool eq_graph_has_children(const eq_graph_t* eq, eq_node_id_t id) {
  return eq_graph_get_children(eq, id) != NULL;
}

static
bool eq_graph_is_term(const eq_graph_t* eq, eq_node_id_t n_id) {
  const eq_node_t* n = eq_graph_get_node_const(eq, n_id);
  return n->type == EQ_NODE_TERM;
}

static
bool eq_graph_is_value(const eq_graph_t* eq, eq_node_id_t n_id) {
  const eq_node_t* n = eq_graph_get_node_const(eq, n_id);
  return n->type == EQ_NODE_VALUE;
}

static
bool eq_graph_is_pair(const eq_graph_t* eq, eq_node_id_t n_id) {
  const eq_node_t* n = eq_graph_get_node_const(eq, n_id);
  return n->type == EQ_NODE_PAIR || n->type == EQ_NODE_EQ_PAIR;
}

/** Add a value node */
eq_node_id_t eq_graph_add_value(eq_graph_t* eq, const mcsat_value_t* v);

/** Is this value registered yet? */
bool eq_graph_has_value(const eq_graph_t* eq, const mcsat_value_t* v);

/** Return the id of a value */
eq_node_id_t eq_graph_value_id(const eq_graph_t* eq, const mcsat_value_t* v);

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
  init_pmap2(&eq->eq_pair_to_id);

  init_ivector(&eq->kind_list, 0);
  init_ivector(&eq->terms_list, 0);
  init_value_vector(&eq->values_list, 0);
  init_ivector(&eq->pair_list, 0);

  scope_holder_construct(&eq->scope_holder);

  init_ivector(&eq->graph, 0);

  init_pmap2(&eq->pair_to_rep);
  init_pmap2(&eq->eq_pair_to_rep);

  init_merge_queue(&eq->merge_queue, 0);
  init_ivector(&eq->merges, 0);

  init_ivector(&eq->term_value_merges, 0);

  init_ivector(&eq->uselist, 0);
  init_ivector(&eq->uselist_updates, 0);

  init_ivector(&eq->children_list, 0);
  init_int_hmap(&eq->node_to_children, 0);

  // Add true/false
  eq->true_node_id = eq_graph_add_value(eq, &mcsat_value_true);
  eq->false_node_id = eq_graph_add_value(eq, &mcsat_value_false);

  init_term_manager(&eq->tm, eq->ctx->terms);
  eq->tm.simplify_ite = false;

  eq->graph_out = 0;

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
  delete_pmap2(&eq->eq_pair_to_id);

  delete_ivector(&eq->kind_list);
  delete_ivector(&eq->terms_list);
  delete_value_vector(&eq->values_list);
  delete_ivector(&eq->pair_list);

  scope_holder_destruct(&eq->scope_holder);

  delete_ivector(&eq->graph);

  delete_pmap2(&eq->pair_to_rep);
  delete_pmap2(&eq->eq_pair_to_rep);

  delete_merge_queue(&eq->merge_queue);
  delete_ivector(&eq->merges);

  delete_ivector(&eq->term_value_merges);

  safe_free(eq->uselist_nodes);

  delete_ivector(&eq->uselist);
  delete_ivector(&eq->uselist_updates);

  delete_ivector(&eq->children_list);
  delete_int_hmap(&eq->node_to_children);

  delete_term_manager(&eq->tm);
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
eq_node_id_t eq_graph_new_node(eq_graph_t* eq, eq_node_type_t type, uint32_t index) {

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
  eq_node_id_t id = eq_graph_new_node(eq, EQ_NODE_KIND, index);
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
  eq_node_id_t id = eq_graph_new_node(eq, EQ_NODE_TERM, index);
  find->val = id;

  assert(eq->nodes_size == eq->graph.size);
  assert(eq->kind_list.size + eq->terms_list.size + eq->values_list.size + eq->pair_list.size / 2 == eq->nodes_size);

  // If the node is a constant, we also create a value for it
  bool is_const = is_const_term(eq->ctx->terms, t);
  if (is_const) {
    mcsat_value_t t_value;
    mcsat_value_construct_from_constant_term(&t_value, eq->ctx->terms, t);
    eq_node_id_t v_id = eq_graph_add_value(eq, &t_value);
    mcsat_value_destruct(&t_value);
    merge_queue_push_init(&eq->merge_queue, id, v_id, REASON_IS_CONSTANT_DEF, 0);
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
  eq_node_id_t id = eq_graph_new_node(eq, EQ_NODE_VALUE, index);
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

/**
 * Adds a pair. If n_children > 0 it will associate the children with the pair
 * in fun_children_array. If the pair is already there it will pop the children
 * of the eq->children array
 */
eq_node_id_t eq_graph_add_pair(eq_graph_t* eq, eq_node_type_t type, eq_node_id_t p1, eq_node_id_t p2, uint32_t children_size, uint32_t children_start) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_add_pair[%s]()\n", eq->name);
  }

  assert(type == EQ_NODE_PAIR || type == EQ_NODE_EQ_PAIR);
  assert(type != EQ_NODE_EQ_PAIR || children_size > 0);

  // Check if already there
  pmap2_t* cache = type == EQ_NODE_PAIR ? &eq->pair_to_id : &eq->eq_pair_to_id;
  pmap2_rec_t* find = pmap2_get(cache, p1, p2);
  if (find->val >= 0) {
    if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
      ctx_trace_printf(eq->ctx, "already there: %"PRIi32"\n", find->val);
    }
    // Remove from children array
    if (children_size > 0) {
      assert(eq->children_list.size == children_start + children_size + 1); // + 1 for null
      ivector_shrink(&eq->children_list, children_start);
    }
    return find->val;
  }

  // Index where we put the value
  uint32_t index = eq->pair_list.size;
  ivector_push(&eq->pair_list, p1);
  ivector_push(&eq->pair_list, p2);

  // Setup the new node
  eq_node_id_t id = eq_graph_new_node(eq, type, index);
  find->val = id;

  // Remember the children
  if (children_size > 0) {
    int_hmap_add(&eq->node_to_children, id, children_start);
  }

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

  assert(n->type == EQ_NODE_PAIR || n->type == EQ_NODE_EQ_PAIR);
  // n1
  eq_node_id_t p1 = eq->pair_list.data[n->index];
  const eq_node_t* n1 = eq_graph_get_node_const(eq, p1);
  // n2
  eq_node_id_t p2 = eq->pair_list.data[n->index + 1];
  const eq_node_t* n2 = eq_graph_get_node_const(eq, p2);

  // Store normalized pair or merge if someone is already there
  pmap2_t* rep_cache = n->type == EQ_NODE_PAIR ? &eq->pair_to_rep : &eq->eq_pair_to_rep;
  pmap2_rec_t* find = pmap2_get(rep_cache, n1->find, n2->find);
  if (find->val < 0) {
    // New representative
    find->val = pair_id;
  } else {
    // Merge with existing representative
    if (find->val != pair_id) {
      merge_queue_push_init(&eq->merge_queue, pair_id, find->val, REASON_IS_CONGRUENCE, 0);
    }
  }

  // If equality we check for propagation
  if (n->type == EQ_NODE_EQ_PAIR) {
    // Check for symmetry
    if (n1->find != n2->find) {
      find = pmap2_find(rep_cache, n2->find, n1->find);
      if (find != NULL && find->val != pair_id) {
        merge_queue_push_init(&eq->merge_queue, pair_id, find->val, REASON_IS_CONGRUENCE_EQ_SYM, 0);
      }
    }
    // Check for reflexivity and evaluation
    eq_graph_eq_args_updated(eq, pair_id);
  }
}

/** Generic function add */
static
eq_node_id_t eq_graph_add_fun_term(eq_graph_t* eq, term_t t, term_t f_term, term_kind_t f_kind, uint32_t n, const term_t* c_terms) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_add_fun_term[%s](): ", eq->name);
    ctx_trace_term(eq->ctx, t);
  }

  assert(n >= 1);
  assert(f_term == NULL_TERM || f_kind == UNINTERPRETED_TERM);

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

  // Where we put the children
  uint32_t children_start = eq->children_list.size;
  uint32_t children_size = 0;

  // Add the function itself
  eq_node_type_t final_pair_type;
  if (f_kind == UNINTERPRETED_TERM) {
    assert(f_term != NULL_TERM);
    eq_node_id_t c = eq_graph_add_term(eq, f_term);
    ivector_push(&eq->children_list, c);
    children_size ++;
    final_pair_type = EQ_NODE_PAIR;
  } else {
    assert(f_term == NULL_TERM);
    if (f_kind == EQ_TERM) {
      final_pair_type = EQ_NODE_EQ_PAIR;
    } else {
      eq_node_id_t c = eq_graph_add_kind(eq, f_kind);
      ivector_push(&eq->children_list, c);
      children_size ++;
      final_pair_type = EQ_NODE_PAIR;
    }
  }

  // Add the real children
  uint32_t i = 0;
  for (i = 0; i < n; ++ i) {
    eq_node_id_t c = eq_graph_add_term(eq, c_terms[i]);
    ivector_push(&eq->children_list, c);
    children_size ++;
  }
  ivector_push(&eq->children_list, eq_node_null);
  const eq_node_id_t* c_nodes = (const eq_node_id_t*) eq->children_list.data + children_start;

  // Add the pairs for children
  assert(children_size >= 2);
  i = children_size - 1;
  eq_node_id_t p2 = c_nodes[i];
  for (-- i; i > 0; -- i) {
    eq_node_id_t p1 = c_nodes[i];
    // Add the graph node (p1, p2) with children if root
    p2 = eq_graph_add_pair(eq, EQ_NODE_PAIR, p1, p2, 0, 0);
    // Store in the hash table
    eq_graph_update_pair_hash(eq, p2);
  }

  // Add the final one for the whole function (NOTE!!! if already there, it will pop children NOTE!!!)
  p2 = eq_graph_add_pair(eq, final_pair_type, c_nodes[0], p2, children_size, children_start);

  // Store in the hash table
  eq_graph_update_pair_hash(eq, p2);

  // Add the equality f = p2
  merge_queue_push_init(&eq->merge_queue, f_id, p2, REASON_IS_FUNCTION_DEF, 0);

  // We added lots of stuff, maybe there were merges
  eq_graph_propagate(eq);

  return f_id;
}

eq_node_id_t eq_graph_add_ufun_term(eq_graph_t* eq, term_t t, term_t f, uint32_t n, const term_t* children) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_ufun_term[%s](): ", eq->name);
    ctx_trace_term(eq->ctx, t);
  }

  return eq_graph_add_fun_term(eq, t, f, UNINTERPRETED_TERM, n, children);
}

eq_node_id_t eq_graph_add_ifun_term(eq_graph_t* eq, term_t t, term_kind_t f, uint32_t n, const term_t* children) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq")) {
    ctx_trace_printf(eq->ctx, "eq_graph_ifun_term[%s](): ", eq->name);
    ctx_trace_term(eq->ctx, t);
  }

  return eq_graph_add_fun_term(eq, t, NULL_TERM, f, n, children);
}


eq_node_id_t eq_graph_term_id(const eq_graph_t* eq, term_t t) {
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &eq->term_to_id, t);
  assert(find != NULL);
  return find->val;
}

eq_node_id_t eq_graph_term_id_if_exists(const eq_graph_t* eq, term_t t) {
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &eq->term_to_id, t);
  if (find != NULL) {
    return find->val;
  } else {
    return eq_node_null;
  }
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

void eq_graph_print_node(const eq_graph_t* eq, const eq_node_t* n, FILE* out, bool print_extra) {
  eq_node_id_t n_id = eq_graph_get_node_id(eq, n);
  switch (n->type) {
  case EQ_NODE_KIND: {
    term_kind_t kind = eq->kind_list.data[n->index];
    fprintf(out, "%s", kind_to_string(kind));
    if (print_extra) {
      fprintf(out, "(id=%"PRIu32", idx=%"PRIu32")", n_id, n->index);
    }
    break;
  }
  case EQ_NODE_TERM: {
    term_t t = eq->terms_list.data[n->index];
    term_print_to_file(out, eq->ctx->terms, t);
    if (print_extra) {
      fprintf(out, " (id=%"PRIu32", idx=%"PRIu32")", n_id, n->index);
    }
    break;
  }
  case EQ_NODE_VALUE: {
    const mcsat_value_t* v = eq->values_list.data + n->index;
    mcsat_value_print(v, out);
    if (print_extra) {
      fprintf(out, " (id=%"PRIu32", idx=%"PRIu32")", n_id, n->index);
    }
    break;
  }
  case EQ_NODE_EQ_PAIR:
    fprintf(out, "[= ");
    eq_node_id_t p1 = eq->pair_list.data[n->index];
    eq_graph_print_node(eq, eq_graph_get_node_const(eq, p1), out, false);
    fprintf(out, " ");
    eq_node_id_t p2 = eq->pair_list.data[n->index + 1];
    eq_graph_print_node(eq, eq_graph_get_node_const(eq, p2), out, false);
    fprintf(out, "]");
    if (print_extra) {
      fprintf(out, " (id=%"PRIu32", idx=%"PRIu32")", n_id, n->index);
    }
    break;
  case EQ_NODE_PAIR: {
    fprintf(out, "[");
    eq_node_id_t p1 = eq->pair_list.data[n->index];
    eq_graph_print_node(eq, eq_graph_get_node_const(eq, p1), out, false);
    fprintf(out, ", ");
    eq_node_id_t p2 = eq->pair_list.data[n->index + 1];
    eq_graph_print_node(eq, eq_graph_get_node_const(eq, p2), out, false);
    fprintf(out, "]");
    if (print_extra) {
      fprintf(out, " (id=%"PRIu32", idx=%"PRIu32")", n_id, n->index);
    }
    break;
  }
  }

  if (print_extra) {
    const eq_node_id_t* children = eq_graph_get_children(eq, n_id);
    if (children != NULL) {
      fprintf(out, " {");
      const eq_node_id_t* it = children;
      for (; *it != eq_node_null; ++it) {
        if (it != children) {
          fprintf(out, ", ");
        }
        const eq_node_t* n = eq_graph_get_node_const(eq, *it);
        eq_graph_print_node(eq, n, out, false);
      }
      fprintf(out, "}");
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
    // Only print representatives
    if (n->find == i) {
      fprintf(out, "  ");
      eq_graph_print_node(eq, n, out, true);
      fprintf(out, ": ");
      eq_graph_print_class(eq, n->find, out);
      fprintf(out, "\n");
    }
  }
}

void eq_graph_to_gv_init(const eq_graph_t* eq, const char* filename) {
  assert(eq->graph_out == NULL);

  // Open the file
  eq_graph_t* eq_nonconst = (eq_graph_t *) eq;
  eq_nonconst->graph_out = fopen(filename, "w");

  // Header
  fprintf(eq->graph_out, "graph G1 {\n\n");
  fprintf(eq->graph_out, "  node [shape=record, style=filled];\n\n");

  // All the nodes
  uint32_t i;
  for (i = 0; i < eq->nodes_size; ++ i) {
    const eq_node_t* n = eq_graph_get_node_const(eq, i);
    fprintf(eq->graph_out, "  n%"PRIu32" [label=\"", i);
    eq_graph_print_node(eq, n, eq->graph_out, false);
    fprintf(eq->graph_out, "\"];\n");
  }

  // All the edges (they come in pairs)
  fprintf(eq->graph_out, "\n");
  for (i = 0; i < eq->edges_size; i += 2) {
    const eq_edge_t* e = eq->edges + i;
    fprintf(eq->graph_out, "  n%"PRIu32" -- n%"PRIu32" [label=\"%s\"]\n", e->u, e->v, eq_graph_reason_to_short_string(e->reason.type));
  }
}

void eq_graph_to_gv_edge(const eq_graph_t* eq, const eq_edge_t* e, uint32_t id) {
  if (eq->graph_out != NULL) {
    fprintf(eq->graph_out, "  n%"PRIu32" -- n%"PRIu32" [label=\"%d\"]\n", e->u, e->v, id);
  }
}

void eq_graph_to_gv_mark_node(const eq_graph_t* eq, eq_node_id_t n_id) {
  if (eq->graph_out != NULL) {
    fprintf(eq->graph_out, "\n  n%"PRIu32" [color=red, fillcolor=lightgray];\n", n_id);
  }
}

void eq_graph_to_gv_done(const eq_graph_t* eq) {
  assert(eq->graph_out != NULL);

  // Footer
  fprintf(eq->graph_out, "}\n");

  // Close the file
  eq_graph_t* eq_nonconst = (eq_graph_t *) eq;
  fclose(eq_nonconst->graph_out);
  eq_nonconst->graph_out = NULL;
}

static
void eq_graph_update_find(eq_graph_t* eq, eq_node_id_t n_id, eq_node_id_t find) {
  // Update the find in n2's class
  eq_node_t* it = eq_graph_get_node(eq, n_id);
  assert(it->find != find);
  do {
    assert(it->type != EQ_NODE_VALUE);
    it->find = find;
    it = eq_graph_get_node(eq, it->next);
  } while (it->find != find);
}

/** Merge node n2 into n1 */
static
void eq_graph_merge_nodes(eq_graph_t* eq, eq_node_id_t n_into_id, eq_node_id_t n_from_id) {

  eq_node_t* n_into = eq_graph_get_node(eq, n_into_id);
  eq_node_t* n_from = eq_graph_get_node(eq, n_from_id);

  assert(n_into->type != EQ_NODE_VALUE || n_from->type != EQ_NODE_VALUE);

  assert(n_into->find == n_into_id);
  assert(n_from->find == n_into_id); // Nodes have been updated already
  assert(n_into_id != n_from_id);

  // Finally merge the lists (circular lists)
  eq_node_id_t tmp = n_into->next;
  n_into->next = n_from->next;
  n_from->next = tmp;

  // Update the size
  n_into->size += n_from->size;
}

/** Un-merge node n2 from n1 */
static
void eq_graph_unmerge_nodes(eq_graph_t* eq, eq_node_id_t n_into_id, eq_node_id_t n_from_id) {

  eq_node_t* n_into = eq_graph_get_node(eq, n_into_id);
  eq_node_t* n_from = eq_graph_get_node(eq, n_from_id);

  assert(n_into->find == n_into_id);
  assert(n_from->find == n_into_id);
  assert(n_into_id != n_from_id);

  // Update the size
  assert(n_into->size > n_from->size);
  n_into->size -= n_from->size;

  // Unmerge the lists (circular lists)
  eq_node_id_t tmp = n_into->next;
  n_into->next = n_from->next;
  n_from->next = tmp;
}


/** Do we prefer n1 to n2 */
static inline
bool eq_graph_merge_preference(const eq_node_t* n1, const eq_node_t* n2) {

  // Value terms have precedence (if both values, we have a conflict so we don't care)
  if (n2->type == EQ_NODE_VALUE) {
    return false;
  }
  if (n1->type == EQ_NODE_VALUE) {
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

  assert(!eq->in_conflict);

  // edge between pairs and terms/values is only acceptable if the pair has children (root pair)
  assert(!eq_graph_is_term(eq, n1) || !eq_graph_is_pair(eq, n2) || eq_graph_has_children(eq, n2));
  assert(!eq_graph_is_term(eq, n2) || !eq_graph_is_pair(eq, n1) || eq_graph_has_children(eq, n1));
  assert(!eq_graph_is_value(eq, n1) || !eq_graph_is_pair(eq, n2) || eq_graph_has_children(eq, n2));
  assert(!eq_graph_is_value(eq, n2) || !eq_graph_is_pair(eq, n1) || eq_graph_has_children(eq, n1));

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

/** class of n has been updated, update the pairs */
static
void eq_graph_update_lookups(eq_graph_t* eq, eq_node_id_t n_id) {
  // Go through class of n
  eq_node_id_t i = n_id;
  do {
    // Go through uselist of i
    eq_uselist_id_t j = eq->uselist.data[i];
    while (j != eq_uselist_null) {
      const eq_uselist_t* ul = eq->uselist_nodes + j;
      // Update the pair
      eq_graph_update_pair_hash(eq, ul->node);
      j = ul->next;
    }
    i = eq_graph_get_node(eq, i)->next;
  } while (i != n_id);
}

static inline
const mcsat_value_t* eq_graph_get_value(const eq_graph_t* eq, eq_node_id_t n_id) {
  const eq_node_t* n = eq_graph_get_node_const(eq, n_id);
  assert(n->type == EQ_NODE_VALUE);
  return eq->values_list.data + n->index;
}

static inline
term_t eq_graph_get_term(const eq_graph_t* eq, eq_node_id_t n_id) {
  const eq_node_t* n = eq_graph_get_node_const(eq, n_id);
  assert(n->type == EQ_NODE_TERM);
  return eq->terms_list.data[n->index];
}
static
void eq_graph_eq_assigned_to_value(eq_graph_t* eq, eq_node_id_t eq_id, eq_node_id_t v_id) {
  const mcsat_value_t* v = eq_graph_get_value(eq, v_id);
  if (mcsat_value_is_true(v)) {
    // x = y -> true, merge x, y
    // children[0] == EQ_TERM_id
    const eq_node_t* eq_node = eq_graph_get_node_const(eq, eq_id);
    assert(eq_node->type == EQ_NODE_EQ_PAIR);
    eq_node_id_t lhs = eq->pair_list.data[eq_node->index];
    eq_node_id_t rhs = eq->pair_list.data[eq_node->index + 1];
    merge_queue_push_init(&eq->merge_queue, lhs, rhs, REASON_IS_TRUE_EQUALITY, eq_id);
  }
}

static
void eq_graph_eq_args_updated(eq_graph_t* eq, eq_node_id_t eq_id) {
  const eq_node_t* eq_node = eq_graph_get_node_const(eq, eq_id);
  assert(eq_node->type == EQ_NODE_EQ_PAIR);
  eq_node_id_t lhs_id = eq->pair_list.data[eq_node->index];
  const eq_node_t* lhs_node = eq_graph_get_node_const(eq, lhs_id);
  eq_node_id_t rhs_id = eq->pair_list.data[eq_node->index + 1];
  const eq_node_t* rhs_node = eq_graph_get_node_const(eq, rhs_id);

  if (lhs_node->find == rhs_node->find) {
    // If arguments equal, can evaluate
    merge_queue_push_init(&eq->merge_queue, eq_id, eq->true_node_id, REASON_IS_REFLEXIVITY, eq_id);
  } else {
    // If arguments are constants, we can evaluate
    const eq_node_t* lhs_find = eq_graph_get_node_const(eq, lhs_node->find);
    if (lhs_find->type == EQ_NODE_VALUE) {
      const eq_node_t* rhs_find = eq_graph_get_node_const(eq, rhs_node->find);
      if (rhs_find->type == EQ_NODE_VALUE) {
        // finds are distinct, so we evaluate to false
        merge_queue_push_init(&eq->merge_queue, eq_id, eq->false_node_id, REASON_IS_EVALUATION, eq_id);
      }
    }
  }

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
    eq_node_id_t lhs = merge->lhs;
    eq_node_id_t rhs = merge->rhs;
    const eq_node_t* n1 = eq_graph_get_node_const(eq, lhs);
    const eq_node_t* n2 = eq_graph_get_node_const(eq, rhs);
    eq_reason_t reason = merge->reason;
    merge_queue_pop(&eq->merge_queue);

    if (ctx_trace_enabled(eq->ctx, "mcsat::eq::propagate")) {
      ctx_trace_printf(eq->ctx, "eq_graph_propagate[%s]()\n", eq->name);
      ctx_trace_printf(eq->ctx, "n1 = "); eq_graph_print_node(eq, n1, ctx_trace_out(eq->ctx), true); ctx_trace_printf(eq->ctx, "\n");
      ctx_trace_printf(eq->ctx, "n2 = "); eq_graph_print_node(eq, n2, ctx_trace_out(eq->ctx), true); ctx_trace_printf(eq->ctx, "\n");
      ctx_trace_printf(eq->ctx, "reason = %s\n", eq_graph_reason_to_string(reason.type));
    }

    // Check if already equal
    if (n1->find == n2->find) {
      continue;
    }

    // We merge n_from into n_into
    eq_node_id_t n_into_id = n1->find;
    const eq_node_t* n_into = eq_graph_get_node_const(eq, n_into_id);
    eq_node_id_t n_from_id = n2->find;
    const eq_node_t* n_from = eq_graph_get_node_const(eq, n_from_id);
    // Swap if we prefer n2_find to be the representative
    if (eq_graph_merge_preference(n_from, n_into)) {
      const eq_node_t* tmp1 = n_into; n_into = n_from; n_from = tmp1;
      eq_node_id_t tmp2 = n_into_id; n_into_id = n_from_id; n_from_id = tmp2;
    }

    // Add the edge (original nodes)
    eq_graph_add_edge(eq, lhs, rhs, reason);

    // If we merge two same-type nodes that are constant we have a conflict
    if (n_from->type == EQ_NODE_VALUE && n_into->type == EQ_NODE_VALUE) {
      if (ctx_trace_enabled(eq->ctx, "mcsat::conflict::check")) {
        FILE* out = ctx_trace_out(eq->ctx);
        fprintf(out, "TRAIL\n");
        trail_print(eq->ctx->trail, out);
        fprintf(out, "GRAPH\n");
        eq_graph_print(eq, out);
        fprintf(out, "into = "); eq_graph_print_node(eq, eq_graph_get_node_const(eq, n_into->find), out, false); fprintf(out, "\n");
        fprintf(out, "from = "); eq_graph_print_node(eq, eq_graph_get_node_const(eq, n_from->find), out, false); fprintf(out, "\n");
      }
      eq->in_conflict = true;
      eq->conflict_lhs = n_into->find;
      eq->conflict_rhs = n_from->find;
      // Done
      continue;
    }

    // If we merge into a value
    if (n_into->type == EQ_NODE_VALUE) {
      // Process the nodes updated to a constant
      eq_node_id_t it_id = n_from_id;
      const eq_node_t* it = n_from;
      do {

        // Terms we notify as being propagated to values
        if (it->type == EQ_NODE_TERM) {
          ivector_push(&eq->term_value_merges, it_id);
        }

        // Interpreted terms, might propagate something useful
        if (it->type == EQ_NODE_EQ_PAIR) {
          eq_graph_eq_assigned_to_value(eq, it_id, n_into_id);
        }

        // Next node
        it_id = it->next;
        it = eq_graph_get_node(eq, it_id);

      } while (it != n_from);

    }

    // Update finds
    eq_graph_update_find(eq, n_from_id, n_into_id);

    // Update lookups
    eq_graph_update_lookups(eq, n_from_id);

    // Merge n2 into n1
    eq_graph_merge_nodes(eq, n_into_id, n_from_id);

    // Remember the merge
    ivector_push(&eq->merges, n_into_id);
    ivector_push(&eq->merges, n_from_id);
  }

  // Done, clear
  merge_queue_reset(&eq->merge_queue);
  eq->in_propagate = false;
}

void eq_graph_assert_eq(eq_graph_t* eq, eq_node_id_t lhs, eq_node_id_t rhs,
    eq_reason_type_t reason_type, uint32_t reason_data) {

  assert(lhs < eq->nodes_size);
  assert(rhs < eq->nodes_size);
  assert(lhs != rhs);

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::propagate")) {
    ctx_trace_printf(eq->ctx, "eq_graph_assert_eq[%s]()\n", eq->name);
    ctx_trace_printf(eq->ctx, "lhs = "); eq_graph_print_node(eq, eq_graph_get_node(eq, lhs), ctx_trace_out(eq->ctx), true); ctx_trace_printf(eq->ctx, "\n");
    ctx_trace_printf(eq->ctx, "rhs = "); eq_graph_print_node(eq, eq_graph_get_node(eq, rhs), ctx_trace_out(eq->ctx), true); ctx_trace_printf(eq->ctx, "\n");
    ctx_trace_printf(eq->ctx, "reason = %s\n", eq_graph_reason_to_string(reason_type));
  }

  // Enqueue for propagation
  merge_queue_push_init(&eq->merge_queue, lhs, rhs, reason_type, reason_data);

  // Propagate
  eq_graph_propagate(eq);
}

void eq_graph_assert_term_eq(eq_graph_t* eq, term_t lhs, term_t rhs, uint32_t reason_data) {
  eq_node_id_t lhs_id = eq_graph_add_term(eq, lhs);
  eq_node_id_t rhs_id = eq_graph_add_term(eq, rhs);
  eq_graph_assert_eq(eq, lhs_id, rhs_id, REASON_IS_USER, reason_data);
}

bool eq_graph_has_propagated_terms(const eq_graph_t* eq) {
  return eq->term_value_merges.size > 0;
}

void eq_graph_get_propagated_terms(eq_graph_t* eq, ivector_t* out_terms) {
  // Copy over the terms that are equal to a value
  uint32_t i;
  for (i = 0; i < eq->term_value_merges.size; ++ i) {
    eq_node_id_t n_id = eq->term_value_merges.data[i];
    const eq_node_t* n = eq_graph_get_node_const(eq, n_id);
    eq_node_id_t n_find_id = n->find;
    const eq_node_t* n_find = eq_graph_get_node_const(eq, n_find_id);
    assert(n->type == EQ_NODE_TERM && n_find->type == EQ_NODE_VALUE);
    ivector_push(out_terms, eq->terms_list.data[n->index]);
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
      eq_graph_assert_eq(eq, v_id, x_id, REASON_IS_IN_TRAIL, x);
    }
  }
}

void eq_graph_push(eq_graph_t* eq) {

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::detail")) {
    ctx_trace_printf(eq->ctx, "eq_graph_push[%s]()\n", eq->name);
    eq_graph_print(eq, ctx_trace_out(eq->ctx));
  }

  assert(!eq->in_conflict);
  assert(eq->term_value_merges.size == 0);
  assert(merge_queue_is_empty(&eq->merge_queue));

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
      &eq->children_list.size,
      &eq->merges.size,
      NULL
  );

  // Push the pair maps
  pmap2_push(&eq->pair_to_id);
  pmap2_push(&eq->eq_pair_to_id);
  pmap2_push(&eq->pair_to_rep);
  pmap2_push(&eq->eq_pair_to_rep);

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
  uint32_t children_list_size;
  uint32_t merges_size;

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
      &children_list_size,
      &merges_size,
      NULL
  );

  uint32_t i;

  // Remove any added edges
  const eq_edge_t* edge = eq->edges + eq->edges_size;
  while (eq->edges_size > edges_size) {
    edge --;
    eq->edges_size --;
    eq->graph.data[edge->u] = edge->next;
  }

  // Unmerge the nodes, in order
  while (eq->merges.size > merges_size) {
    eq_node_id_t from_id = ivector_pop2(&eq->merges);
    eq_node_id_t into_id = ivector_pop2(&eq->merges);
    // Un-merge the two nodes
    eq_graph_unmerge_nodes(eq, into_id, from_id);
    // Reverse the finds
    eq_graph_update_find(eq, from_id, from_id);
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

  // Remove the added nodes and their children
  for (i = nodes_size; i < eq->nodes_size; ++ i) {
    int_hmap_pair_t* find = int_hmap_find(&eq->node_to_children, i);
    if (find != NULL) {
      int_hmap_erase(&eq->node_to_children, find);
      assert(eq_graph_is_pair(eq, i));
    } else {
      assert(!eq_graph_is_pair(eq, i));
    }
  }
  eq->nodes_size = nodes_size;

  // Pop the graph size
  ivector_shrink(&eq->graph, graph_size);

  // Pop the pair maps
  pmap2_pop(&eq->pair_to_id);
  pmap2_pop(&eq->eq_pair_to_id);
  pmap2_pop(&eq->pair_to_rep);
  pmap2_pop(&eq->eq_pair_to_rep);

  // Pop the children
  ivector_shrink(&eq->children_list, children_list_size);

  // Reset the merge queue
  merge_queue_reset(&eq->merge_queue);

  // Clear conflict
  eq->in_conflict = false;
  eq->conflict_lhs = eq_node_null;
  eq->conflict_rhs = eq_node_null;

  // Reset any propagations
  ivector_reset(&eq->term_value_merges);

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::detail")) {
    ctx_trace_printf(eq->ctx, "eq_graph_pop[%s](): after\n", eq->name);
    eq_graph_print(eq, ctx_trace_out(eq->ctx));
  }
}

/**
 * Make an equality between two terms that evaluates to true wrt the given values.
 */
term_t eq_graph_add_eq_explanation(const eq_graph_t* eq,
    term_t lhs, eq_node_id_t lhs_value,
    term_t rhs, eq_node_id_t rhs_value,
    ivector_t* reasons_data, ivector_t* reasons_type) {

  bool is_boolean = is_boolean_term(eq->ctx->terms, lhs);
  assert(is_boolean == is_boolean_term(eq->ctx->terms, rhs));

  if (!is_boolean) {
    // Proper values, make an equality and negate if not true in the trail
    term_t equality = mk_eq((term_manager_t*) &eq->tm, lhs, rhs);
    term_t to_add = equality;
    if (lhs_value != rhs_value) {
      to_add = opposite_term(to_add);
    }
    if (ctx_trace_enabled(eq->ctx, "mcsat::eq::explain")) {
      ctx_trace_printf(eq->ctx, "created new:");
      ctx_trace_term(eq->ctx, to_add);
    }
    assert(term_kind(eq->ctx->terms, equality) == EQ_TERM);
    ivector_push(reasons_data, to_add);
    if (reasons_type != NULL) {
      ivector_push(reasons_type, REASON_IS_IN_TRAIL);
    }
    return equality;
  } else {
    if (lhs_value == eq->false_node_id) lhs = opposite_term(lhs);
    if (rhs_value == eq->false_node_id) rhs = opposite_term(rhs);
    ivector_push(reasons_data, lhs);
    ivector_push(reasons_data, rhs);
    if (reasons_type != NULL) {
      ivector_push(reasons_type, REASON_IS_IN_TRAIL);
      ivector_push(reasons_type, REASON_IS_IN_TRAIL);
    }
    return NULL_TERM;
  } }

/**
 * Terms t1 and t2, corresponding to a path n1 -- n2, such that:
 *
 * - if n1 is a term => t1 = n1
 * - if n2 is a term => t2 = n2
 * - t1 != null => t1 == n1 and can evaluate to a value in the trail,
 * - t2 != null => t2 == n2 and can evaluate to a value in the trail,
 * - if there is a term or value node in the path => t1 or t2 != null
 * - if t1 = t2 then t1 = t2 = null
 *
 * Examples (edges):
 *
 * - [FUNCTION_DEF]  f(x) - [f x]: t1 = f(x), t2 = null
 *                   [f x] = f(x): t1 = null, t2 = f(x)
 * - [CONSTANT_DEF]  T - true: t1 = null, t2 = true
 *                   true - T: t1 = true, t2 = null
 * - [CONGRUENCE]    [f x] - [f y]: t1 = null, t2 = null
 * - [TRUE_EQUALITY] x - y: t1 = x, t2 = y
 * - [REFLEXIVITY]   [= x y] - T: t1 = null, t2 = true
 *                   T - [= x y]: t1 = true, t2 = null
 * - [EVALUATION]    [= x y] - F: t1 = (x_t2 = y_t2), t2 = null, with x == x_t2, y == y_t2
 *                   F - [= x y]: t1 = null, t2 = (x_t2 = y_t2), with x == x_t2, y == y_t2
 * - [IN_TRAIL]      0 - x: t1 = null, t2 = x
 * - [IN_TRAIL]      x - 1: t1 = x, t2 = null
 * - [USER]          x - y: t1 = x, t2 = y
 *
 * Examples (paths):
 * - x -t- 1 -t- y: t1 = x, t2 = y
 * - 1 -t- f(x) -c- f(y) -- 0: first = f(x), last = f(y)
 * - (x = y) -d- [= x y] -r- T: first = (x = y), last = true
 * - [= x y] -d- (x = y) -t- T: last = (x = y), last = (x = y)
 */
typedef struct {
  term_t t1;
  term_t t2;
} path_terms_t;

/** Explain the path from n1 to n2. */
static
path_terms_t eq_graph_explain(const eq_graph_t* eq, eq_node_id_t n1_id, eq_node_id_t n2_id, ivector_t* reasons_data, ivector_t* reasons_type);

/** Explain the edge e (from u to v) */
static
path_terms_t eq_graph_explain_edge(const eq_graph_t* eq, const eq_edge_t* e, ivector_t* reasons_data, ivector_t* reasons_type) {

  static int depth = 0;

  depth ++;

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::explain")) {
    ctx_trace_printf(eq->ctx, "[%d] explaining:", depth);
    eq_graph_print_node(eq, eq_graph_get_node_const(eq, e->u), ctx_trace_out(eq->ctx), true);
    ctx_trace_printf(eq->ctx, " == ");
    eq_graph_print_node(eq, eq_graph_get_node_const(eq, e->v), ctx_trace_out(eq->ctx), true);
    ctx_trace_printf(eq->ctx, " because of %s\n", eq_graph_reason_to_string(e->reason.type));
  }

  // The edge nodes
  const eq_node_t* u = eq_graph_get_node_const(eq, e->u);
  const eq_node_t* v = eq_graph_get_node_const(eq, e->v);

  // Default term results
  path_terms_t terms = { NULL_TERM, NULL_TERM };
  if (u->type == EQ_NODE_TERM) { terms.t1 = eq_graph_get_term(eq, e->u); }
  if (v->type == EQ_NODE_TERM) { terms.t2 = eq_graph_get_term(eq, e->v); }

  // Default: no value

  // Add to reason
  switch (e->reason.type) {
  case REASON_IS_FUNCTION_DEF:
  case REASON_IS_IN_TRAIL:
  case REASON_IS_CONSTANT_DEF:
    // Nothing to do really, terms already added
    break;
  case REASON_IS_USER: {
    // User added, nothing to do, but add to reasons
    ivector_push(reasons_data, e->reason.data);
    if (reasons_type != NULL) {
      ivector_push(reasons_type, REASON_IS_USER);
    }
    break;
  }
  case REASON_IS_TRUE_EQUALITY: {
    // Get the reason of the equality and explain why it's true
    eq_node_id_t eq_id = e->reason.data;
    path_terms_t eq_explain = eq_graph_explain(eq, eq_id, eq->true_node_id, reasons_data, reasons_type);
    assert(eq_explain.t1 != NULL_TERM);
    ivector_push(reasons_data, eq_explain.t1);
    if (reasons_type != NULL) {
      ivector_push(reasons_type, REASON_IS_IN_TRAIL);
    }
    break;
  }
  case REASON_IS_CONGRUENCE: {
    // Get the reasons of the arguments
    // We are guaranteed that these are top-level function nodes
    const eq_node_id_t* u_c = eq_graph_get_children(eq, e->u);
    const eq_node_id_t* v_c = eq_graph_get_children(eq, e->v);
    while (*u_c != eq_node_null) {
      assert(*v_c != eq_node_null);
      if (*u_c != *v_c) {
        assert(eq_graph_get_node_const(eq, *u_c)->type == EQ_NODE_TERM);
        assert(eq_graph_get_node_const(eq, *v_c)->type == EQ_NODE_TERM);
        eq_graph_explain(eq, *u_c, *v_c, reasons_data, reasons_type);
      }
      u_c ++;
      v_c ++;
    }
    assert (*v_c == eq_node_null);
    // First last stay null, these are both non-terms
    break;
  }
  case REASON_IS_CONGRUENCE_EQ_SYM: {
    // Speciall case for eq with symmetry
    const eq_node_id_t* u_c = eq_graph_get_children(eq, e->u);
    const eq_node_id_t* v_c = eq_graph_get_children(eq, e->v);
    if (u_c[0] != v_c[1]) {
      eq_graph_explain(eq, u_c[0], v_c[1], reasons_data, reasons_type);
    }
    if (u_c[1] != v_c[0]) {
      eq_graph_explain(eq, u_c[1], v_c[0], reasons_data, reasons_type);
    }
    // First last stay null, these are both non-terms
    break;
  }
  case REASON_IS_REFLEXIVITY: {
    // Get the reason of the equality
    eq_node_id_t eq_id = e->reason.data;
    const eq_node_t* eq_node = eq_graph_get_node_const(eq, eq_id);
    assert(eq_node->type == EQ_NODE_EQ_PAIR);
    eq_node_id_t lhs_id = eq->pair_list.data[eq_node->index];
    eq_node_id_t rhs_id = eq->pair_list.data[eq_node->index+1];
    eq_graph_explain(eq, lhs_id, rhs_id, reasons_data, reasons_type);
    // Add the evaluation terms
    if (u->type == EQ_NODE_VALUE) { terms.t1 = true_term; }
    if (v->type == EQ_NODE_VALUE) { terms.t2 = true_term; }
    break;
  }
  case REASON_IS_EVALUATION: {
    // Get the reason of the equality
    eq_node_id_t eq_id = e->reason.data;
    const eq_node_t* eq_node = eq_graph_get_node_const(eq, eq_id);
    assert(eq_node->type == EQ_NODE_EQ_PAIR);
    eq_node_id_t lhs_id = eq->pair_list.data[eq_node->index];
    eq_node_id_t rhs_id = eq->pair_list.data[eq_node->index + 1];
    const eq_node_t* lhs_node = eq_graph_get_node_const(eq, lhs_id);
    const eq_node_t* rhs_node = eq_graph_get_node_const(eq, rhs_id);
    // Explain lhs = lhs_value
    eq_node_id_t lhs_value_id = lhs_node->find;
    assert(eq_graph_is_value(eq, lhs_value_id));
    path_terms_t lhs_explain = eq_graph_explain(eq, lhs_id, lhs_value_id, reasons_data, reasons_type);
    // Explain rhs = rhs_value
    eq_node_id_t rhs_value_id = rhs_node->find;
    assert(eq_graph_is_value(eq, rhs_value_id));
    path_terms_t rhs_explain = eq_graph_explain(eq, rhs_id, rhs_value_id, reasons_data, reasons_type);
    // Part of explanation also lhs_value != rhs_value
    assert(lhs_explain.t2 != NULL_TERM);
    assert(rhs_explain.t2 != NULL_TERM);
    term_t reason_eq = eq_graph_add_eq_explanation(eq, lhs_explain.t2, lhs_value_id, rhs_explain.t2, rhs_value_id, reasons_data, reasons_type);
    assert(reason_eq != NULL_TERM);
    // Set the first/last
    if (u->type == EQ_NODE_EQ_PAIR) { terms.t1 = reason_eq; }
    if (v->type == EQ_NODE_EQ_PAIR) { terms.t2 = reason_eq; }
    break;
  }
  default:
    assert(false);
  }

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::explain")) {
    ctx_trace_printf(eq->ctx, "[%d] t1 = ", depth);
    if (terms.t1 == NULL_TERM) ctx_trace_printf(eq->ctx, "NULL\n");
    else ctx_trace_term(eq->ctx, terms.t1);
    ctx_trace_printf(eq->ctx, "[%d] t2 = ", depth);
    if (terms.t2 == NULL_TERM) ctx_trace_printf(eq->ctx, "NULL\n");
    else ctx_trace_term(eq->ctx, terms.t2);
  }

  depth --;

  return terms;
}

/**
 * Explain why n1 is equal to n2 (both terms or values).
 *
 * A path from n1 to n2 goes through edges. We also remember the term closest
 * to n1 as t1, and term closest to n2 as t2.
 *
 * Usage:
 * 1. Conflicts: explain(conflict_lhs, conflict_rhs), both constants
 * 2. Propagations: explain(t, v), t is term deduced equal to value v,
 *
 * Example 1: x -t- 0 -t- y in the graph, explain x = y for congruence
 *
 * Returns A => t1 =:= t2 such that
 * (1) each a in A can evaluate to true trail (or is added by user)
 * (2) A => t1 = t2 is true universally
 * (3a) t1 is closest term to n1 that can evaluate to same value as n1
 * (3b) t2 is closest term to n2 that can evaluate to same value as n2
 *
 * A is a added to reasons data, t1, t2 is in returned value.
 *
 * Reason types contains the reason (IN_TRAIL, or USER).
 *
 * Result usage:
 *
 * 1. Conflicts:
 *    - assert A => (t1 = t2), it is universally valid and (t1 == t2)
 *    - A evaluates to true in the trail
 *    - t1 = t2 must evaluate to false in the trail (n1 != n2, 3a, 3b)
 * 2. Propagations:
 *    - explanation A with substitution t2 for t
 *    - each A can evaluate to true in the trail (or is added by user)
 *    - t2 must evaluate to v in the trail
 */
static
path_terms_t eq_graph_explain(const eq_graph_t* eq, eq_node_id_t n1_id, eq_node_id_t n2_id, ivector_t* reasons_data, ivector_t* reasons_type) {

  uint32_t current_explain_id = ((eq_graph_t*)eq)->explain_id ++;

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::explain")) {
    ctx_trace_printf(eq->ctx, "eq_graph_explain[%s]()\n", eq->name);
    ctx_trace_printf(eq->ctx, "n1 = ");
    eq_graph_print_node(eq, eq_graph_get_node_const(eq, n1_id), ctx_trace_out(eq->ctx), true);
    ctx_trace_printf(eq->ctx, "\n");
    ctx_trace_printf(eq->ctx, "n2 = ");
    eq_graph_print_node(eq, eq_graph_get_node_const(eq, n2_id), ctx_trace_out(eq->ctx), true);
    ctx_trace_printf(eq->ctx, "\n");
    ctx_trace_printf(eq->ctx, "explain id = %d\n", eq->explain_id);
  }

  // Don't explain same nodes
  assert (n1_id != eq_node_null);
  assert (n2_id != eq_node_null);
  assert (n1_id != n2_id);

  // Run BFS:
  // - there has to be a path from n1 to n2 (since equal)
  // - the graph is a tree hence visit once (since we only merge non-equal)

  ivector_t bfs_queue;
  init_ivector(&bfs_queue, 0);
  ivector_push(&bfs_queue, n1_id);

  int_hmap_t edges_used; // Map from node to the edge that got to it
  init_int_hmap(&edges_used, 0);
  int_hmap_add(&edges_used, n1_id, INT32_MAX);

  bool path_found = false;
  uint32_t bfs_i = 0;
  for (; !path_found; bfs_i ++) {

    // Get the current node
    assert(bfs_i < bfs_queue.size);
    eq_node_id_t n_id = bfs_queue.data[bfs_i];

    if (ctx_trace_enabled(eq->ctx, "mcsat::eq::explain")) {
      ctx_trace_printf(eq->ctx, "BFS node:");
      eq_graph_print_node(eq, eq_graph_get_node_const(eq, n_id), ctx_trace_out(eq->ctx), true);
      ctx_trace_printf(eq->ctx, "\n");
    }

    // Go through the edges
    eq_edge_id_t n_edge = eq->graph.data[n_id];
    while (!path_found && n_edge != eq_edge_null) {
      const eq_edge_t* e = eq->edges + n_edge;
      assert(n_id == e->u);

      // Did we find a path
      if (e->v == n2_id) {
        path_found = true;
      }

      // The only way to visit a node again, is through back-edges, skip them
      int_hmap_pair_t* edge_find = int_hmap_get(&edges_used, e->v);
      if (edge_find->val < 0) {
        if (ctx_trace_enabled(eq->ctx, "mcsat::eq::explain")) {
          ctx_trace_printf(eq->ctx, "BFS edge:");
          eq_graph_print_node(eq, eq_graph_get_node_const(eq, e->u), ctx_trace_out(eq->ctx), true);
          ctx_trace_printf(eq->ctx, " -> ");
          eq_graph_print_node(eq, eq_graph_get_node_const(eq, e->v), ctx_trace_out(eq->ctx), true);
          ctx_trace_printf(eq->ctx, "\n");
        }
        // Add to queue and record the edge
        ivector_push(&bfs_queue, e->v);
        edge_find->val = n_edge;
      }

      // Next edge
      n_edge = e->next;
    }
  }

  assert(path_found);

  // First and last terms in the path
  path_terms_t path_terms = { NULL_TERM, NULL_TERM };
  // Term assigned to value that we didn't explain yet
  term_t t2_to_explain = NULL_TERM;
  // Value it was assigned to
  eq_node_id_t value_to_explain = eq_node_null;

  // Start from the back
  eq_node_id_t n_id = n2_id;

  // Reconstruct the path
  for(;;) {

    // Relevant path edge of the node
    int_hmap_pair_t* find = int_hmap_find(&edges_used, n_id);
    eq_edge_id_t n_edge = find->val;
    // If we hit the end marker, we're done
    if (n_edge == INT32_MAX) {
      break;
    }

    const eq_edge_t* e = eq->edges + n_edge;
    assert(e->v == n_id);
    if (ctx_trace_enabled(eq->ctx, "mcsat::eq::explain")) {
      eq_graph_to_gv_edge(eq, e, current_explain_id);
    }


    // Explain the edge
    path_terms_t e_terms = eq_graph_explain_edge(eq, e, reasons_data, reasons_type);

    // Last term
    if (path_terms.t2 == NULL_TERM) {
      if (e_terms.t2 != NULL_TERM) { path_terms.t2 = e_terms.t2; }
      else if (e_terms.t1 != NULL_TERM) { path_terms.t2 = e_terms.t1; }
    }
    // First term
    if (e_terms.t2 != NULL_TERM) { path_terms.t1 = e_terms.t2; }
    if (e_terms.t1 != NULL_TERM) { path_terms.t1 = e_terms.t1; }

    // If we have a term evaluation to explain, explain it if possible
    if (t2_to_explain != NULL_TERM) {
      // See if we have a term to explain with
      term_t t1_to_explain = NULL_TERM;
      if (e_terms.t2 != NULL_TERM) {
        t1_to_explain = e_terms.t2;
      } else if (e_terms.t1 != NULL_TERM) {
        t1_to_explain = e_terms.t1;
      }
      if (t1_to_explain != NULL_TERM) {
        // We now add to explanation that t1 - value - t2
        eq_graph_add_eq_explanation(eq, t1_to_explain, value_to_explain, t2_to_explain, value_to_explain, reasons_data, reasons_type);
        // Explained, reset
        t2_to_explain = NULL_TERM;
        value_to_explain = eq_node_null;
      }
    }

    // Check if we passed a value assignment that we need to explain
    if (e->reason.type == REASON_IS_IN_TRAIL) {
      if (e_terms.t2 != NULL_TERM) {
        assert(t2_to_explain == NULL_TERM && value_to_explain == eq_node_null);
        t2_to_explain = e_terms.t2;
        value_to_explain = e->u;
      }
    }

    // Next back in the path
    n_id = e->u;
  }

  // Finally, if there is an assignment left unexplained, it has to be
  // last in the path, so it's up to the user to add the explanation
  assert(t2_to_explain == NULL_TERM || t2_to_explain == path_terms.t1);

  delete_int_hmap(&edges_used);
  delete_ivector(&bfs_queue);

  assert(path_terms.t2 != NULL_TERM);

  // This is false: it can happen, for example
  // (= x y) - [= x y] - false, where last edge is due to evaluation
  // x - 0, y - 1.
  // assert(result.t2_id != n1_id);

  return path_terms;
}

void eq_graph_get_conflict(const eq_graph_t* eq, ivector_t* conflict_data, ivector_t* conflict_types) {

  ((eq_graph_t*)eq)->explain_id = 0;

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::conflict")) {
    ctx_trace_printf(eq->ctx, "eq_graph_get_conflict[%s]()\n", eq->name);

    static int count = 0;
    count ++;
    char filename[100];
    sprintf(filename, "conflict_%d.gv", count);
    eq_graph_to_gv_init(eq, filename);
    eq_graph_to_gv_mark_node(eq, eq->conflict_lhs);
    eq_graph_to_gv_mark_node(eq, eq->conflict_rhs);
  }

  path_terms_t result = eq_graph_explain(eq, eq->conflict_lhs, eq->conflict_rhs, conflict_data, conflict_types);
  assert(result.t1 != result.t2);
  // This one can have value here: e.g., when f(x) != f(y) is asserted
  // and f(x) -> 0, f(y) -> 1 is asserted. If the we're explaining why
  // 0 = 1, if it's due to congruence f(x) = f(y), we need add
  // explanation f(x) != f(y)
  // assert(!eq_graph_check_trail_value(eq, t1_eq_t2, false));
  eq_graph_add_eq_explanation(eq, result.t1, eq->conflict_lhs, result.t2, eq->conflict_rhs, conflict_data, conflict_types);

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::conflict")) {
    ctx_trace_printf(eq->ctx, "eq_graph_get_conflict[%s]()\n", eq->name);
    uint32_t i = 0;
    for (i = 0; i < conflict_data->size; ++ i) {
      ctx_trace_printf(eq->ctx, "[%"PRIu32"]: ", i);
      ctx_trace_term(eq->ctx, conflict_data->data[i]);
    }
    eq_graph_to_gv_done(eq);
  }
}

term_t eq_graph_explain_term_propagation(const eq_graph_t* eq, term_t t, ivector_t* explain_data, ivector_t* explain_types) {

  ((eq_graph_t*) eq)->explain_id = 0;

  eq_node_id_t t_id = eq_graph_term_id(eq, t);
  const eq_node_t* t_node = eq_graph_get_node_const(eq, t_id);
  assert(t_node->type == EQ_NODE_TERM);
  eq_node_id_t v_id = t_node->find;
  assert(eq_graph_get_node_const(eq, v_id)->type == EQ_NODE_VALUE);

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::propagate")) {
    ctx_trace_printf(eq->ctx, "eq_graph_explain_term_propagation[%s]()\n", eq->name);
    static int count = 0;
    count ++;
    char filename[100];
    sprintf(filename, "propagation_%d.gv", count);
    eq_graph_to_gv_init(eq, filename);
    eq_graph_to_gv_mark_node(eq, t_id);
    eq_graph_to_gv_mark_node(eq, v_id);
  }

  path_terms_t result = eq_graph_explain(eq, t_id, v_id, explain_data, explain_types);
  assert(result.t2 != NULL_TERM);

  if (ctx_trace_enabled(eq->ctx, "mcsat::eq::propagate")) {
    ctx_trace_printf(eq->ctx, "eq_graph_explain_term_propagation[%s]()\n", eq->name);
    ctx_trace_printf(eq->ctx, "t = ");
    ctx_trace_term(eq->ctx, t);
    ctx_trace_printf(eq->ctx, "v = ");
    mcsat_value_print(eq_graph_get_value(eq, v_id), ctx_trace_out(eq->ctx));
    ctx_trace_printf(eq->ctx, "\n");
    eq_graph_to_gv_done(eq);
    uint32_t i = 0;
    for (i = 0; i < explain_data->size; ++ i) {
      ctx_trace_printf(eq->ctx, "[%"PRIu32"]: ", i);
      ctx_trace_term(eq->ctx, explain_data->data[i]);
    }

    ctx_trace_printf(eq->ctx, "t_in: ");
    ctx_trace_term(eq->ctx, t);
    ctx_trace_printf(eq->ctx, "t_out: ");
    ctx_trace_term(eq->ctx, result.t2);
  }

  // This can happen: for example explain: (= x y) - [= x y] - false because of
  // evaluation x - 0, y - 1. Substitution (= x y) is valid, if it evaluates
  // to false.
  //
  // If it doesn't evaluate do false, i.e., if x - a - 0, y - b - 1, we need
  // to return (= a b) as substitution for (= x y).
  //
  assert(result.t2 != t);
  return result.t2;
}

