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
#include "tracing.h"

#include <inttypes.h>
#include <assert.h>

void equality_graph_construct(equality_graph_t* eq, plugin_context_t* ctx, const char* name) {
  eq->ctx = ctx;

  eq->capacity = 0;
  eq->size = 0;
  eq->graph_nodes = 0;

  eq->name = name;

  init_int_hmap(&eq->term_to_id, 0);
  init_value_hmap(&eq->value_to_id, 0);
  init_ivector(&eq->terms_list, 0);
  init_value_vector(&eq->values_list, 0);

  scope_holder_construct(&eq->scope_holder);

  // Add true/false
  equality_graph_add_value(eq, &mcsat_value_true);
  equality_graph_add_value(eq, &mcsat_value_false);
}

void equality_graph_destruct(equality_graph_t* eq) {
  safe_free(eq->graph_nodes);

  delete_int_hmap(&eq->term_to_id);
  delete_value_hmap(&eq->value_to_id);
  delete_ivector(&eq->terms_list);
  delete_value_vector(&eq->values_list);
}

// Default initial size and max size
#define DEFAULT_GRAPH_SIZE 10
#define MAX_GRAPH_SIZE (UINT32_MAX/sizeof(equality_graph_node_t))

static
equality_graph_node_t* equality_graph_new_node(equality_graph_t* eq) {
  uint32_t n = eq->size;

  // Check if we need to resize
  if (n == eq->capacity) {
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
    eq->graph_nodes = (equality_graph_node_t*) safe_realloc(eq->graph_nodes, n * sizeof(equality_graph_node_t));
    eq->capacity = n;
  }

  // Return the new element
  return &eq->graph_nodes[eq->size ++];
}

bool equality_graph_add_term(equality_graph_t* eq, term_t t) {

  // New id of the node
  uint32_t id = eq->size;
  uint32_t index = eq->terms_list.size;

  // Check if already there
  int_hmap_pair_t* find = int_hmap_get(&eq->term_to_id, t);
  if (find->val < 0) {
    find->val = id;
    ivector_push(&eq->terms_list, t);
  } else {
    return false;
  }

  // Setup the new node
  equality_graph_node_t* node = equality_graph_new_node(eq);
  node->find = id;
  node->next = id;
  node->index = index;
  node->is_value = false;

  assert(eq->terms_list.size + eq->values_list.size == eq->size);

  // Added, done
  return true;
}

bool equality_graph_add_value(equality_graph_t* eq, const mcsat_value_t* v) {

  // New id of the node
  uint32_t id = eq->size;
  uint32_t index = eq->values_list.size;

  // Check if already there
  value_hmap_pair_t* find = value_hmap_get(&eq->value_to_id, v);
  if (find->val < 0) {
    find->val = id;
    value_vector_push(&eq->values_list);
    mcsat_value_t* v_copy = value_vector_last(&eq->values_list);
    mcsat_value_assign(v_copy, v);
  } else {
    return false;
  }

  // Setup the new node
  equality_graph_node_t* node = equality_graph_new_node(eq);
  node->find = id;
  node->next = id;
  node->index = index;
  node->is_value = true;

  assert(eq->terms_list.size + eq->values_list.size == eq->size);

  // Added, done
  return true;
}

static
equality_graph_node_id equality_graph_term_id(const equality_graph_t* eq, term_t t) {
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &eq->term_to_id, t);
  assert(find != NULL);
  return find->val;
}

static
equality_graph_node_id equality_graph_value_id(const equality_graph_t* eq, const mcsat_value_t* v) {
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

void equality_graph_print_class(const equality_graph_t* eq, equality_graph_node_id start_node_id, FILE* out) {
  const equality_graph_node_t* n = eq->graph_nodes + start_node_id;
  bool first = true;
  do {
    if (!first) { fprintf(out, ", "); }
    if (n->is_value) {
      const mcsat_value_t* v = eq->values_list.data + n->index;
      uint32_t n_id = n - eq->graph_nodes;
      mcsat_value_print(v, out);
      fprintf(out, "(id=%"PRIu32", idx=%"PRIu32")", n->index, n_id);
    } else {
      term_t t = eq->terms_list.data[n->index];
      uint32_t n_id = n - eq->graph_nodes;
      term_print_to_file(out, eq->ctx->terms, t);
      fprintf(out, "(id=%"PRIu32", idx=%"PRIu32")", n->index, n_id);
    }
    n = eq->graph_nodes + n->next;
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
    equality_graph_node_id t_id = equality_graph_term_id(eq, t);
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
