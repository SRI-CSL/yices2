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

#include <stdbool.h>

#include <poly/poly.h>
#include <poly/polynomial_context.h>
#include <poly/feasibility_set_int.h>
#include <poly/polynomial.h>
#include <poly/upolynomial.h>

#include "mcsat/ff/ff_feasible_set_db.h"
#include "utils/int_vectors.h"
#include "utils/ptr_hash_map.h"
#include "mcsat/tracing.h"
#include "mcsat/variable_db.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/utils/value_version_set.h"
#include "ff_plugin_internal.h"
#include "utils/int_array_sort2.h"


/**
 * Element in the list. Each element contains a pointer to the previous
 * version, the reason for the update (reason) and its feasible set, and
 * the new feasible set.
 */
typedef struct {
  /** Next element */
  uint32_t prev;
  /** Reasons for the update, if one then constraint, otherwise disjunction */
  variable_t* reasons;
  /** Size of the reasons */
  uint32_t reasons_size;
  /** The new total feasible set (i.e. feasible set of all asserted constraints) */
  lp_feasibility_set_int_t* feasible_set;
  /** The feasible set of the reason (feasible = feasible intersect this) */
  lp_feasibility_set_int_t* reason_feasible_set;

} feasibility_list_element_t;

struct ff_feasible_set_db_struct {
  /** Elements of the lists */
  feasibility_list_element_t* memory;

  /** The currently occupied memory size */
  uint32_t memory_size;

  /** The capacity of the memory */
  uint32_t memory_capacity;

  /** Map from variables to the first element (current feasible set) */
  int_hmap_t var_to_feasible_set_map;

  /** Variables that were updated, so we can backtrack */
  ivector_t updates;

  /** Size of the updates array, so that we can backtrack */
  uint32_t updates_size;

  /** All variables that were fixed */
  ivector_t fixed_variables;

  /** Size of the fixed variables array, for backtracking */
  uint32_t fixed_variable_size;

  /** Index into the fixed variables */
  uint32_t fixed_variables_i;

  /** Scope for push/pop */
  scope_holder_t scope;

  /** the plugin */
  ff_plugin_t* plugin;
};

static
uint32_t feasible_set_db_get_index(const ff_feasible_set_db_t* db, variable_t x) {
  int_hmap_pair_t* find = int_hmap_find(&db->var_to_feasible_set_map, x);
  if (find == NULL) {
    return 0;
  } else {
    return find->val;
  }
}

static
void ff_feasible_set_element_delete(feasibility_list_element_t *element) {
  // Deallocate allocated data
  lp_feasibility_set_int_t* s1 = element->feasible_set;
  lp_feasibility_set_int_t* s2 = element->reason_feasible_set;
  lp_feasibility_set_int_delete(s1);
  if (s1 != s2) {
    lp_feasibility_set_int_delete(s2);
  }
  safe_free(element->reasons);
}

#define INITIAL_DB_SIZE 100

/** Create a new database */
ff_feasible_set_db_t* ff_feasible_set_db_new(ff_plugin_t* plugin) {
  ff_feasible_set_db_t* db = safe_malloc(sizeof(ff_feasible_set_db_t));

  db->memory_size = 1;
  db->memory_capacity = INITIAL_DB_SIZE;
  db->memory = safe_malloc(sizeof(feasibility_list_element_t) * db->memory_capacity);

  init_int_hmap(&db->var_to_feasible_set_map, 0);
  init_ivector(&db->updates, 0);
  init_ivector(&db->fixed_variables, 0);

  db->updates_size = 0;
  db->fixed_variable_size = 0;
  db->fixed_variables_i = 0;

  scope_holder_construct(&db->scope);

  db->plugin = plugin;

  return db;
}

/** Delete the database */
void ff_feasible_set_db_delete(ff_feasible_set_db_t* db) {
  // Delete the feasible sets
  // Start from 1, 0 is special.
  for (uint32_t i = 1; i < db->memory_size; ++ i) {
    ff_feasible_set_element_delete(db->memory + i);
  }
  // Delete the other stuff
  delete_int_hmap(&db->var_to_feasible_set_map);
  delete_ivector(&db->updates);
  delete_ivector(&db->fixed_variables);
  scope_holder_destruct(&db->scope);

  // Free the memory
  safe_free(db->memory);
  safe_free(db);
}

lp_feasibility_set_int_t* ff_feasible_set_db_get(ff_feasible_set_db_t* db, variable_t x) {
  uint32_t index = feasible_set_db_get_index(db, x);
  if (index == 0) {
    return NULL;
  } else {
    return db->memory[index].feasible_set;
  }
}

/** Print the feasible sets of given variable */
void ff_feasible_set_db_print_var(ff_feasible_set_db_t* db, variable_t var, FILE* out) {
  fprintf(out, "Feasible sets of ");
  variable_db_print_variable(db->plugin->ctx->var_db, var, out);
  fprintf(out, " :\n");
  uint32_t index = feasible_set_db_get_index(db, var);
  while (index != 0) {
    feasibility_list_element_t* current = db->memory + index;
    fprintf(out, "\t");
    lp_feasibility_set_int_print(current->feasible_set, out);
    fprintf(out, "\n\t\t");
    lp_feasibility_set_int_print(current->reason_feasible_set, out);
    fprintf(out, "\n");
    if (current->reasons_size > 1) {
      fprintf(out, "\t\tDue to lemma\n");
    } else {
      fprintf(out, "\t\tDue to ");
      term_t reason_term = variable_db_get_term(db->plugin->ctx->var_db, current->reasons[0]);
      term_print_to_file(out, db->plugin->ctx->terms, reason_term);
      if (term_type_kind(db->plugin->ctx->terms, reason_term) == BOOL_TYPE) {
        // Otherwise it's a term evaluation, always true
        fprintf(out, " assigned to %s\n", trail_get_boolean_value(db->plugin->ctx->trail, current->reasons[0]) ? "true" : "false");
      }
    }
    index = current->prev;
  }
}

/** Print the feasible set database */
void ff_feasible_set_db_print(ff_feasible_set_db_t* db, FILE* out) {
  int_hmap_pair_t* it;
  for (it = int_hmap_first_record(&db->var_to_feasible_set_map); it != NULL; it = int_hmap_next_record(&db->var_to_feasible_set_map, it)) {

    variable_t var = it->key;
    fprintf(out, "Feasible sets of ");
    variable_db_print_variable(db->plugin->ctx->var_db, var, out);
    fprintf(out, " :\n");
    if (trail_has_value(db->plugin->ctx->trail, var)) {
      fprintf(out, "\tassigned to: ");
      const mcsat_value_t* var_value = trail_get_value(db->plugin->ctx->trail, var);
      mcsat_value_print(var_value, out);
      fprintf(out, "\n");
    }

    uint32_t index = it->val;
    while (index != 0) {
      feasibility_list_element_t* current = db->memory + index;
      fprintf(out, "\t");
      lp_feasibility_set_int_print(db->memory[index].feasible_set, out);
      fprintf(out, "\n\t\t");
      lp_feasibility_set_int_print(db->memory[index].reason_feasible_set, out);
      fprintf(out, "\n");
      index = current->prev;
    }
  }
}

static inline
void ff_feasible_set_db_ensure_memory(ff_feasible_set_db_t* db) {
  if (db->memory_size >= db->memory_capacity) {
    db->memory_capacity = db->memory_capacity + db->memory_capacity / 2;
    db->memory = safe_realloc(db->memory, db->memory_capacity * sizeof(feasibility_list_element_t));
  }
  assert(db->memory_size < db->memory_capacity);
}

bool ff_feasible_set_db_update(ff_feasible_set_db_t* db, variable_t x, lp_feasibility_set_int_t* new_set, const variable_t* reasons, size_t reasons_count) {
  if (ctx_trace_enabled(db->plugin->ctx, "ff::feasible_set_db")) {
    fprintf(ctx_trace_out(db->plugin->ctx), "ff_feasible_set_db_update\n");
    ff_feasible_set_db_print(db, ctx_trace_out(db->plugin->ctx));
  }

  assert(db->updates_size == db->updates.size);

  bool feasible = true;

  // The one we're adding
  lp_feasibility_set_int_t* intersect = NULL;

  // Intersect, if no difference, we're done
  const lp_feasibility_set_int_t* old_set = ff_feasible_set_db_get(db, x);

  if (old_set != NULL) {
    if (ctx_trace_enabled(db->plugin->ctx, "ff::feasible_set_db")) {
      ctx_trace_printf(db->plugin->ctx, "ff_feasible_set_db_update()\n");
      ctx_trace_printf(db->plugin->ctx, "old_set = ");
      lp_feasibility_set_int_print(old_set, ctx_trace_out(db->plugin->ctx));
      ctx_trace_printf(db->plugin->ctx, "\nnew_set = ");
      lp_feasibility_set_int_print(new_set, ctx_trace_out(db->plugin->ctx));
      ctx_trace_printf(db->plugin->ctx, "\n");
    }

    assert(!lp_feasibility_set_int_is_empty(old_set));
    lp_feasibility_set_int_status_t status;
    intersect = lp_feasibility_set_int_intersect_with_status(old_set, new_set, &status);
    switch (status) {
    case LP_FEASIBILITY_SET_INT_S1:
      // old set stays
      lp_feasibility_set_int_delete(new_set);
      lp_feasibility_set_int_delete(intersect);
      return true;
    case LP_FEASIBILITY_SET_INT_S2:
    case LP_FEASIBILITY_SET_INT_NEW:
      // we have a new set
      break;
    case LP_FEASIBILITY_SET_INT_EMPTY:
      feasible = false;
      break;
    }
  } else {
    feasible = !lp_feasibility_set_int_is_empty(new_set);
    intersect = new_set;
  }

  // Get the previous
  uint32_t prev = feasible_set_db_get_index(db, x);

  // Allocate a new one
  uint32_t new_index = db->memory_size;
  // Allocate new element
  db->memory_size ++;
  ff_feasible_set_db_ensure_memory(db);

  // Set up the element
  feasibility_list_element_t* new_element = db->memory + new_index;
  new_element->feasible_set = intersect;
  new_element->reason_feasible_set = new_set;
  new_element->prev = prev;
  // Reasons
  new_element->reasons_size = reasons_count;
  new_element->reasons = safe_malloc(sizeof(variable_t) * reasons_count);
  for (uint32_t i = 0; i < reasons_count; ++ i) {
    new_element->reasons[i] = reasons[i];
  }
  // Add to map
  int_hmap_pair_t* find = int_hmap_find(&db->var_to_feasible_set_map, x);
  if (find == NULL) {
    int_hmap_add(&db->var_to_feasible_set_map, x, new_index);
  } else {
    find->val = new_index;
  }
  // Add to updates list
  ivector_push(&db->updates, x);
  db->updates_size ++;
  assert(db->updates_size == db->updates.size);

  // If fixed, put into the fixed array
  if (lp_feasibility_set_int_is_point(intersect)) {
    ivector_push(&db->fixed_variables, x);
    db->fixed_variable_size ++;
  }

  // Return whether we're feasible
  return feasible;
}

void ff_feasible_set_db_push(ff_feasible_set_db_t *db) {
  scope_holder_push(&db->scope,
    &db->updates_size,
    &db->fixed_variable_size,
    &db->fixed_variables_i,
    NULL
  );
}

void ff_feasible_set_db_pop(ff_feasible_set_db_t* db) {
  if (ctx_trace_enabled(db->plugin->ctx, "ff::ff_feasible_set_db")) {
    fprintf(ctx_trace_out(db->plugin->ctx), "ff_feasible_set_db_pop");
    ff_feasible_set_db_print(db, ctx_trace_out(db->plugin->ctx));
  }

  scope_holder_pop(&db->scope,
    &db->updates_size,
    &db->fixed_variable_size,
    &db->fixed_variables_i,
    NULL
  );

  // Undo fixed variables
  ivector_shrink(&db->fixed_variables, db->fixed_variable_size);

  // Undo updates
  while (db->updates.size > db->updates_size) {
    // The variable that was updated
    variable_t x = ivector_last(&db->updates);
    ivector_pop(&db->updates);
    // Remove the element
    db->memory_size --;
    feasibility_list_element_t* element = db->memory + db->memory_size;
    uint32_t prev = element->prev;
    ff_feasible_set_element_delete(element);
    // Redirect map to the previous one
    int_hmap_pair_t* find = int_hmap_find(&db->var_to_feasible_set_map, x);
    assert(find != NULL);
    assert(find->val == db->memory_size);
    find->val = prev;
  }

  if (ctx_trace_enabled(db->plugin->ctx, "ff::ff_feasible_set_db")) {
    ff_feasible_set_db_print(db, ctx_trace_out(db->plugin->ctx));
  }
}

static
void ff_feasible_set_quickxplain(const ff_feasible_set_db_t* db, const lp_feasibility_set_int_t* current, ivector_t* reasons, uint32_t begin, uint32_t end, ivector_t* out) {

  if (lp_feasibility_set_int_is_empty(current)) {
    // Core already unsat, done
    return;
  }

  assert(begin < end);
  if (begin + 1 == end) {
    // Only one left, we keep it, since the core is still sat
    ivector_push(out, reasons->data[begin]);
    return;
  }

  // Split: how many in first half?
  uint32_t n = (end - begin) / 2;

  // Assert first half and minimize the second
  lp_feasibility_set_int_t* feasible_A = lp_feasibility_set_int_new_copy(current);
  for (uint32_t i = begin; i < begin + n; ++ i) {
    const lp_feasibility_set_int_t* feasible_i = db->memory[reasons->data[i]].reason_feasible_set;
    lp_feasibility_set_int_status_t intersect_status;
    lp_feasibility_set_int_t* intersect = lp_feasibility_set_int_intersect_with_status(feasible_A, feasible_i, &intersect_status);
    lp_feasibility_set_int_swap(intersect, feasible_A);
    lp_feasibility_set_int_delete(intersect);
  }
  uint32_t old_out_size = out->size;
  ff_feasible_set_quickxplain(db, feasible_A, reasons, begin + n, end, out);
  lp_feasibility_set_int_delete(feasible_A);

  // Now, assert the minimized second half, and minimize the first half
  lp_feasibility_set_int_t* feasible_B = lp_feasibility_set_int_new_copy(current);
  for (uint32_t i = old_out_size; i < out->size; ++ i) {
    const lp_feasibility_set_int_t* feasible_i = db->memory[out->data[i]].reason_feasible_set;
    lp_feasibility_set_int_status_t intersect_status;
    lp_feasibility_set_int_t* intersect = lp_feasibility_set_int_intersect_with_status(feasible_B, feasible_i, &intersect_status);
    lp_feasibility_set_int_swap(intersect, feasible_B);
    lp_feasibility_set_int_delete(intersect);
  }
  ff_feasible_set_quickxplain(db, feasible_B, reasons, begin, begin + n, out);
  lp_feasibility_set_int_delete(feasible_B);
}

static
void get_max_degree_max_level(const ff_plugin_t *nra, const feasibility_list_element_t* memory, uint32_t *max_deg, uint32_t *max_lvl) {
  uint32_t deg = 0, lvl = 0;

  for (uint32_t i = 0; i < memory->reasons_size; ++ i) {
    variable_t i_var = memory->reasons[i];
    if (trail_has_value(nra->ctx->trail, i_var)) {
      uint32_t i_lvl = trail_get_level(nra->ctx->trail, i_var);
      if (i_lvl > lvl) {
        lvl = i_lvl;
      }
    }
    const poly_constraint_t* i_constraint = poly_constraint_db_get(nra->constraint_db, i_var);
    const lp_polynomial_t* i_poly = poly_constraint_get_polynomial(i_constraint);
    uint32_t i_deg =  lp_polynomial_degree(i_poly);
    if (i_deg > deg) {
      deg = i_deg;
    }
  }

  *max_deg = deg;
  *max_lvl = lvl;
}

/** Compare variables first by degree, then by level */
static
bool compare_reasons(void *ff_plugin, int32_t r1, int32_t r2) {
  const ff_plugin_t* ff = (ff_plugin_t*) ff_plugin;
  const ff_feasible_set_db_t* db = ff->feasible_set_db;

  // Get max degree and max level of the reasons of both constraints
  uint32_t r1_degree = 0, r2_degree = 0;
  uint32_t r1_level = 0, r2_level = 0;
  get_max_degree_max_level(ff, db->memory + r1, &r1_degree, &r1_level);
  get_max_degree_max_level(ff, db->memory + r2, &r2_degree, &r2_level);

  // Prefer smaller degrees
  if (r1_degree != r2_degree) {
    return r1_degree < r2_degree;
  }

  // Otherwise take the one of lower level
  return r1_level < r2_level;
}

static
void print_conflict_reasons(FILE* out, const ff_feasible_set_db_t* db, ff_plugin_t* ff, ivector_t* reason_indices) {
  poly_constraint_db_t* poly_db = ff->constraint_db;

  for (uint32_t i = 0; i < reason_indices->size; ++ i) {
    fprintf(out, "[%d]: ", i);
    uint32_t r_i = reason_indices->data[i];
    uint32_t r_i_size = db->memory[r_i].reasons_size;
    for (uint32_t j = 0; j < r_i_size; ++ j) {
      if (j) fprintf(out, ", ");
      variable_t r_i_var = db->memory[r_i].reasons[j];
      const poly_constraint_t* r_i_constraint = poly_constraint_db_get(poly_db, r_i_var);
      poly_constraint_print(r_i_constraint, out);
    }
    fprintf(out, "\n");
  }
}

static
void ff_feasible_set_filter_reason_indices(const ff_feasible_set_db_t* db, ivector_t* reasons_indices) {
  ff_plugin_t *ff = db->plugin;
  // The set we're trying to make empty
  lp_feasibility_set_int_t* S = lp_feasibility_set_int_new_full(ff->lp_data->lp_ctx->K);

  // Sort variables by degree and trail level decreasing
  int_array_sort2(reasons_indices->data, reasons_indices->size, (void*) ff, compare_reasons);

  if (ctx_trace_enabled(db->plugin->ctx, "nra::conflict")) {
    ctx_trace_printf(db->plugin->ctx, "filtering: before\n");
    print_conflict_reasons(ctx_trace_out(db->plugin->ctx), db, ff, reasons_indices);
  }

  // Minimize the core
  ivector_t out;
  init_ivector(&out, 0);
  ff_feasible_set_quickxplain(db, S, reasons_indices, 0, reasons_indices->size, &out);
  ivector_swap(reasons_indices, &out);
  delete_ivector(&out);

  // Sort again for consistency
  int_array_sort2(reasons_indices->data, reasons_indices->size, (void*) ff, compare_reasons);

  if (ctx_trace_enabled(db->plugin->ctx, "nra::conflict")) {
    ctx_trace_printf(db->plugin->ctx, "filtering: after\n");
    print_conflict_reasons(ctx_trace_out(db->plugin->ctx), db, ff, reasons_indices);
  }

  // Remove temps
  lp_feasibility_set_int_delete(S);
}

static
void ff_feasible_set_get_conflict_reason_indices(const ff_feasible_set_db_t* db, variable_t x, ivector_t* reasons_indices) {
  // Go back from the top reason for x and gather the indices
  uint32_t reason_index = feasible_set_db_get_index(db, x);
  assert(reason_index);
  while (reason_index) {
    assert(reason_index);
    ivector_push(reasons_indices, reason_index);
    reason_index = db->memory[reason_index].prev;
  }
}

void ff_feasible_set_db_get_conflict_reasons(const ff_feasible_set_db_t* db, variable_t x, ivector_t* reasons_out, ivector_t* lemma_reasons) {

  if (ctx_trace_enabled(db->plugin->ctx, "ff::feasible_set_db")) {
    ctx_trace_printf(db->plugin->ctx, "get_reasons of: ");
    variable_db_print_variable(db->plugin->ctx->var_db, x, ctx_trace_out(db->plugin->ctx));
    ctx_trace_printf(db->plugin->ctx, "\n");
  }

  ivector_t reasons_indices;
  init_ivector(&reasons_indices, 0);

  // Get the indices of the set refinements
  ff_feasible_set_get_conflict_reason_indices(db, x, &reasons_indices);

  ff_feasible_set_filter_reason_indices(db, &reasons_indices);

  // Return the conjunctive reasons
  for (uint32_t i = 0; i < reasons_indices.size; ++ i) {
    uint32_t set_index = reasons_indices.data[i];
    feasibility_list_element_t *element = db->memory + set_index;
    if (element->reasons_size == 1) {
      variable_t reason = element->reasons[0];
      assert(variable_db_is_boolean(db->plugin->ctx->var_db, reason));
      ivector_push(reasons_out, reason);
    } else {
      for (uint32_t j = 0; j < element->reasons_size; ++j) {
        variable_t reason = element->reasons[j];
        assert(variable_db_is_boolean(db->plugin->ctx->var_db, reason));
        ivector_push(lemma_reasons, reason);
      }
    }
  }

  delete_ivector(&reasons_indices);
}

void ff_feasible_set_db_gc_mark(ff_feasible_set_db_t* db, gc_info_t* gc_vars) {
  assert(db->plugin->ctx->trail->decision_level == db->plugin->ctx->trail->decision_level_base);

  if (gc_vars->level == 0) {
    // We keep all the reasons (start from 1, 0 is not used)
    uint32_t element_i, reason_i;
    for (element_i = 1; element_i < db->memory_size; ++ element_i) {
      feasibility_list_element_t* element = db->memory + element_i;
      for (reason_i = 0; reason_i < element->reasons_size; ++ reason_i) {
        gc_info_mark(gc_vars, element->reasons[reason_i]);
      }
    }
  }
}

variable_t ff_feasible_set_db_get_fixed(ff_feasible_set_db_t* db) {
  for (; db->fixed_variables_i < db->fixed_variables.size; ++ db->fixed_variables_i) {
    variable_t var = db->fixed_variables.data[db->fixed_variables_i];
    if (!trail_has_value(db->plugin->ctx->trail, var)) {
      return var;
    }
  }
  return variable_null;
}
