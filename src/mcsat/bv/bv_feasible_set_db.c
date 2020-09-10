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

#include "bv_feasible_set_db.h"
#include "bv_bdd_manager.h"
#include "bv_utils.h"

#include "mcsat/utils/scope_holder.h"
#include "mcsat/tracing.h"
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
  bdd_t feasible_set;
  /** The feasible set of the reason (feasible = feasible intersect this) */
  bdd_t reason_feasible_set;

} feasibility_list_element_t;

struct bv_feasible_set_db_s {

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

  /** The value to manipulate */
  mcsat_value_t tmp_value;

  /** Scope for push/pop */
  scope_holder_t scope;

  /** Plugin context */
  plugin_context_t* ctx;

  /** BDD Manager */
  bv_bdd_manager_t* bddm;

};

static
uint32_t bv_feasible_set_db_get_index(const bv_feasible_set_db_t* db, variable_t x) {
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &db->var_to_feasible_set_map, x);
  if (find == NULL) {
    return 0;
  } else {
    return find->val;
  }
}

void bv_feasible_set_db_print_var(const bv_feasible_set_db_t* db, variable_t var, FILE* out) {

  const variable_db_t* var_db = db->ctx->var_db;

  fprintf(out, "Feasible sets of ");
  variable_db_print_variable(var_db, var, out);
  fprintf(out, " :\n");
  uint32_t index = bv_feasible_set_db_get_index(db, var);
  while (index != 0) {
    feasibility_list_element_t* current = db->memory + index;
    fprintf(out, "\t");
    bv_bdd_manager_bdd_print(db->bddm, current->feasible_set, out);
    fprintf(out, "\n\t\t");
    bv_bdd_manager_bdd_print(db->bddm, current->reason_feasible_set, out);
    fprintf(out, "\n");
    if (current->reasons_size > 1) {
      fprintf(out, "\t\tDue to lemma\n");
    } else {
      fprintf(out, "\t\tDue to ");
      variable_db_print_variable(var_db, current->reasons[0], out);
      if (variable_db_is_boolean(var_db, current->reasons[0]) == BOOL_TYPE) {
        // Otherwise it's a term evaluation, always true
        fprintf(out, " assigned to %s\n", trail_get_boolean_value(db->ctx->trail, current->reasons[0]) ? "true" : "false");
      }
    }
    index = current->prev;
  }
}

void bv_feasible_set_db_print(const bv_feasible_set_db_t* db, FILE* out) {

  int_hmap_pair_t* it = int_hmap_first_record((int_hmap_t*)&db->var_to_feasible_set_map);
  for (; it != NULL; it = int_hmap_next_record((int_hmap_t*)&db->var_to_feasible_set_map, it)) {

    variable_t var = it->key;
    fprintf(out, "Feasible sets of ");
    variable_db_print_variable(db->ctx->var_db, var, out);
    fprintf(out, " :\n");
    if (trail_has_value(db->ctx->trail, var)) {
      fprintf(out, "\tassigned to: ");
      const mcsat_value_t* var_value = trail_get_value(db->ctx->trail, var);
      mcsat_value_print(var_value, out);
      fprintf(out, "\n");
    }

    uint32_t index = it->val;
    while (index != 0) {
      feasibility_list_element_t* current = db->memory + index;
      fprintf(out, "\t");
      bv_bdd_manager_bdd_print(db->bddm, current->feasible_set, out);
      fprintf(out, "\n\t\t");
      bv_bdd_manager_bdd_print(db->bddm, current->reason_feasible_set, out);
      fprintf(out, "\n");
      index = current->prev;
    }
  }
}

#define INITIAL_DB_SIZE 100

bv_feasible_set_db_t* bv_feasible_set_db_new(plugin_context_t* ctx, bv_bdd_manager_t* bddm) {

  bv_feasible_set_db_t* db = safe_malloc(sizeof(bv_feasible_set_db_t));

  db->memory_size = 1; // 0 is special null ref
  db->memory_capacity = INITIAL_DB_SIZE;
  db->memory = safe_malloc(sizeof(feasibility_list_element_t)*db->memory_capacity);
  db->fixed_variable_size = 0;
  db->fixed_variables_i = 0;
  db->updates_size = 0;
  db->ctx = ctx;
  db->bddm = bddm;

  init_int_hmap(&db->var_to_feasible_set_map, 0);
  init_ivector(&db->updates, 0);
  init_ivector(&db->fixed_variables, 0);
  scope_holder_construct(&db->scope);

  mcsat_value_construct_bv_value(&db->tmp_value, NULL);

  return db;
}

void bv_feasible_set_db_delete(bv_feasible_set_db_t* db) {
  // Delete the feasible sets
  uint32_t i;
  // Start from 1, 0 is special.
  for (i = 1; i < db->memory_size; ++ i) {
    safe_free(db->memory[i].reasons);
    bdd_t s1 = db->memory[i].feasible_set;
    bdd_t s2 = db->memory[i].reason_feasible_set;
    bv_bdd_manager_bdd_detach(db->bddm, s1);
    bv_bdd_manager_bdd_detach(db->bddm, s2);
  }
  // Delete the other stuff
  mcsat_value_destruct(&db->tmp_value);
  delete_int_hmap(&db->var_to_feasible_set_map);
  delete_ivector(&db->updates);
  delete_ivector(&db->fixed_variables);
  scope_holder_destruct(&db->scope);
  // Free the memory
  safe_free(db->memory);
  safe_free(db);
}

bdd_t bv_feasible_set_db_get(const bv_feasible_set_db_t* db, variable_t x) {
  uint32_t index = bv_feasible_set_db_get_index(db, x);
  if (index == 0) {
    return bdd_null;
  } else {
    return db->memory[index].feasible_set;
  }
}

const mcsat_value_t* bv_feasible_set_db_pick_value(bv_feasible_set_db_t* db, variable_t x) {

  bool ok;

  // Get the feasible set
  bdd_t x_feasible_bdd = bv_feasible_set_db_get(db, x);
  bool x_feasible_full = x_feasible_bdd.bdd[0] == NULL;

  // Term for x
  term_t x_term = variable_db_get_term(db->ctx->var_db, x);
  uint32_t x_bitsize = term_bitsize(db->ctx->terms, x_term);

  // Check the cached value from the
  const mcsat_trail_t* trail = db->ctx->trail;
  if (trail_has_cached_value(trail, x)) {
    const mcsat_value_t* cached_value = trail_get_cached_value(trail, x);
    if (x_feasible_full) {
      return cached_value;
    } else {
      ok = bv_bdd_manager_is_model(db->bddm, x_term, x_feasible_bdd, &cached_value->bv_value);
      if (ok) { return cached_value; }
    }
  }

  // Initialize the value we're using
  bvconstant_t* value = &db->tmp_value.bv_value;

  // Try simple values: 0, 1, -1

  // 1) Try 0
  bvconstant_set_all_zero(value, x_bitsize);
  if (x_feasible_full) { return &db->tmp_value; }
  ok = bv_bdd_manager_is_model(db->bddm, x_term, x_feasible_bdd, value);
  if (ok) { return &db->tmp_value; }

  // 2) Try 1
  bvconstant_set_one(value);
  ok = bv_bdd_manager_is_model(db->bddm, x_term, x_feasible_bdd, value);
  if (ok) { return &db->tmp_value; }

  // 3) Try -1
  bvconstant_set_all_one(value, x_bitsize);
  ok = bv_bdd_manager_is_model(db->bddm, x_term, x_feasible_bdd, value);
  if (ok) { return &db->tmp_value; }

  // Pick a value from the feasible set
  bv_bdd_manager_pick_value(db->bddm, x_term, x_feasible_bdd, value);

  // Return the constructed value
  return &db->tmp_value;
}

bool bv_feasible_set_db_update(bv_feasible_set_db_t* db, variable_t x, bdd_t new_set, variable_t* cstr_list, uint32_t cstr_count) {

  assert(db->updates_size == db->updates.size);
  bv_bdd_manager_t* bddm = db->bddm;
  //  bool feasible = true; // BD: infer reports a dead store
  bool feasible;
  term_table_t* terms = db->ctx->terms;
  variable_db_t* var_db = db->ctx->var_db;
  term_t x_term = variable_db_get_term(var_db, x);
  uint32_t x_bitsize = bv_term_bitsize(terms, x_term);

  if (ctx_trace_enabled(db->ctx, "bv::feasible_set_db")) {
    fprintf(ctx_trace_out(db->ctx), "bv_feasible_set_db_update: before\n");
    bv_feasible_set_db_print(db, ctx_trace_out(db->ctx));
    fprintf(ctx_trace_out(db->ctx), "adding:");
    bv_bdd_manager_bdd_print(bddm, new_set,  ctx_trace_out(db->ctx));
    fprintf(ctx_trace_out(db->ctx), "\n");
  }

  // The one we're adding
  bdd_t intersect = new_set;
  // Intersect if something to intersect with
  bdd_t old_set = bv_feasible_set_db_get(db, x);

  // Old and new set are managed outside
  if (old_set.bdd[0] != NULL) {
    if (ctx_trace_enabled(db->ctx, "bv::feasible_set_db")) {
      ctx_trace_printf(db->ctx, "bv_feasible_set_db_update()\n");
      ctx_trace_printf(db->ctx, "old_set = ");
      bv_bdd_manager_bdd_print(bddm, old_set, ctx_trace_out(db->ctx));
      ctx_trace_printf(db->ctx, "\nnew_set = ");
      bv_bdd_manager_bdd_print(bddm, new_set, ctx_trace_out(db->ctx));
      ctx_trace_printf(db->ctx, "\n");
    }
    // Intersect with the precious one
    assert(!bv_bdd_manager_bdd_is_empty(bddm, old_set));
    intersect = bv_bdd_manager_bdd_intersect(bddm, old_set, new_set);
    // If new set is the same, nothing to do
    if (bdd_eq(intersect, old_set)) {
      // Old set stays
      bv_bdd_manager_bdd_detach(bddm, intersect);
      return true;
    }
  } else {
    // intersect = new_set, we need to increase reference count for
    // the intersect
    bv_bdd_manager_bdd_attach(bddm, intersect);
  }

  // Are we feasible
  feasible = !bv_bdd_manager_bdd_is_empty(bddm, intersect);

  // Get the previous
  uint32_t prev = bv_feasible_set_db_get_index(db, x);

  // Allocate a new one
  uint32_t new_index = db->memory_size;
  // Allocate new element
  if (db->memory_size == db->memory_capacity) {
    db->memory_capacity = db->memory_capacity + db->memory_capacity/2;
    db->memory = (feasibility_list_element_t*) safe_realloc(db->memory, db->memory_capacity*sizeof(feasibility_list_element_t));
  }
  db->memory_size ++;
  // Setup the element
  feasibility_list_element_t* new_element = db->memory + new_index;
  new_element->feasible_set = intersect; // Intersect attached already
  new_element->reason_feasible_set = new_set;
  bv_bdd_manager_bdd_attach(bddm, new_set); // One more reference
  new_element->prev = prev;
  // Reasons
  new_element->reasons_size = cstr_count;
  new_element->reasons = (variable_t*) safe_malloc(sizeof(variable_t)*cstr_count);
  uint32_t i;
  for (i = 0; i < cstr_count; ++ i) {
    new_element->reasons[i] = cstr_list[i];
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
  if (bv_bdd_manager_bdd_is_point(bddm, new_set, x_bitsize)) {
    ivector_push(&db->fixed_variables, x);
    db->fixed_variable_size ++;
  }

  if (ctx_trace_enabled(db->ctx, "bv::feasible_set_db")) {
    fprintf(ctx_trace_out(db->ctx), "bv_feasible_set_db_update: after:\n");
    bv_feasible_set_db_print(db, ctx_trace_out(db->ctx));
  }

  // Return whether we're feasible
  return feasible;
}

void bv_feasible_set_db_push(bv_feasible_set_db_t* db) {
  scope_holder_push(&db->scope,
     &db->updates_size,
     &db->fixed_variable_size,
     &db->fixed_variables_i,
     NULL
  );
}

void bv_feasible_set_db_pop(bv_feasible_set_db_t* db) {

  if (ctx_trace_enabled(db->ctx, "bv::feasible_set_db")) {
    fprintf(ctx_trace_out(db->ctx), "bv_feasible_set_db_pop");
    bv_feasible_set_db_print(db, ctx_trace_out(db->ctx));
  }

  bv_bdd_manager_t* bddm = db->bddm;

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
    // Release the BDDs
    bdd_t s1 = element->feasible_set;
    bdd_t s2 = element->reason_feasible_set;
    bv_bdd_manager_bdd_detach(bddm, s1);
    bv_bdd_manager_bdd_detach(bddm, s2);
    safe_free(element->reasons);
    // Redirect map to the previous one
    int_hmap_pair_t* find = int_hmap_find(&db->var_to_feasible_set_map, x);
    assert(find != NULL);
    assert(find->val == db->memory_size);
    find->val = prev;
  }

  if (ctx_trace_enabled(db->ctx, "bv::feasible_set_db")) {
    bv_feasible_set_db_print(db, ctx_trace_out(db->ctx));
  }
}

static
void bv_feasible_set_get_reason_indices(const bv_feasible_set_db_t* db, variable_t x, ivector_t* reasons_indices) {
  // Go back from the top reason for x and gather the indices
  uint32_t reason_index = bv_feasible_set_db_get_index(db, x);
  assert(reason_index);
  while (reason_index) {
    assert(reason_index);
    ivector_push(reasons_indices, reason_index);
    reason_index = db->memory[reason_index].prev;
  }
}

static
void bv_feasible_set_quickxplain(const bv_feasible_set_db_t* db, bdd_t current, ivector_t* reasons, uint32_t begin, uint32_t end, ivector_t* out, bv_feasible_explain_mode_t mode, term_t x, const bvconstant_t* x_value, uint32_t bitsize) {

  uint32_t i;
  bv_bdd_manager_t* bddm = db->bddm;

  switch (mode) {
  case EXPLAIN_EMPTY:
    if (bv_bdd_manager_bdd_is_empty(bddm, current)) {
      // Core already unsat, done
      return;
    }
    break;
  case EXPLAIN_SINGLETON:
    if (bv_bdd_manager_bdd_is_point(bddm, current, bitsize)) {
      // Core already implies a point, done
      return;
    }
    break;
  case EXPLAIN_ASSUMPTION:
    if (!bv_bdd_manager_is_model(bddm, x, current, x_value)) {
      // Core doesn't contain the value
      return;
    }
    break;
  default:
    assert(false);
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
  bdd_t feasible_A = current;
  bv_bdd_manager_bdd_attach(bddm, feasible_A);
  for (i = begin; i < begin + n; ++ i) {
    bdd_t feasible_i = db->memory[reasons->data[i]].reason_feasible_set;
    bdd_t intersect = bv_bdd_manager_bdd_intersect(bddm, feasible_A, feasible_i);
    bdd_swap(&intersect, &feasible_A);
    bv_bdd_manager_bdd_detach(bddm, intersect);
  }
  uint32_t old_out_size = out->size;
  bv_feasible_set_quickxplain(db, feasible_A, reasons, begin + n, end, out, mode, x, x_value, bitsize);
  bv_bdd_manager_bdd_detach(bddm, feasible_A);

  // Now, assert the minimized second half, and minimize the first half
  bdd_t feasible_B = current;
  bv_bdd_manager_bdd_attach(bddm, feasible_B);
  for (i = old_out_size; i < out->size; ++ i) {
    bdd_t feasible_i = db->memory[out->data[i]].reason_feasible_set;
    bdd_t intersect = bv_bdd_manager_bdd_intersect(bddm, feasible_B, feasible_i);
    bdd_swap(&intersect, &feasible_B);
    bv_bdd_manager_bdd_detach(bddm, intersect);
  }
  bv_feasible_set_quickxplain(db, feasible_B, reasons, begin, begin + n, out, mode, x, x_value, bitsize);
  bv_bdd_manager_bdd_detach(bddm, feasible_B);
}

/** Compare variables for picking the best explanation */
static
bool bv_feasible_set_compare_reasons(void *bv_feasible_set_db_ptr, int32_t r1, int32_t r2) {

  // TODO: think which constraints are better than others

  uint32_t i;

  bv_feasible_set_db_t* db = (bv_feasible_set_db_t*) bv_feasible_set_db_ptr;
  const mcsat_trail_t* trail = db->ctx->trail;

  // Get max degree and max level of the reasons of first constraint
  uint32_t r1_level = 0;
  for (i = 0; i < db->memory[r1].reasons_size; ++ i) {
    variable_t r1_i_var = db->memory[r1].reasons[i];
    if (trail_has_value(trail, r1_i_var)) {
      uint32_t r1_i_level = trail_get_level(trail, r1_i_var);
      if (r1_i_level > r1_level) {
        r1_level = r1_i_level;
      }
    }
  }

  // Get max degree and max level of the reasons of second constraint
  uint32_t r2_level = 0;
  for (i = 0; i < db->memory[r2].reasons_size; ++ i) {
    variable_t r2_i_var = db->memory[r2].reasons[i];
    if (trail_has_value(trail, r2_i_var)) {
      uint32_t r2_i_level = trail_get_level(trail, r2_i_var);
      if (r2_i_level > r2_level) {
        r2_level = r2_i_level;
      }
    }
  }

  // Pick lower level, break ties by index
  if (r1_level == r2_level) {
    return r1 < r2;
  } else {
    return r1_level < r2_level;
  }
}

static
void print_conflict_reasons(FILE* out, const bv_feasible_set_db_t* db, const ivector_t* reason_indices) {
  uint32_t i, j;
  variable_db_t* var_db = db->ctx->var_db;
  for (i = 0; i < reason_indices->size; ++ i) {
    fprintf(out, "[%d]: ", i);
    uint32_t r_i = reason_indices->data[i];
    uint32_t r_i_size = db->memory[r_i].reasons_size;
    for (j = 0; j < r_i_size; ++ j) {
      if (j) fprintf(out, ", ");
      variable_t r_i_var = db->memory[r_i].reasons[j];
      const mcsat_value_t* v = trail_get_value(db->ctx->trail, r_i_var);
      assert(v->type == VALUE_BOOLEAN);
      fprintf(out, v->b ? "(T) " : "(F) ");
      variable_db_print_variable(var_db, r_i_var, out);
    }
    fprintf(out, "\n");
  }
}

static
void bv_feasible_set_filter_reason_indices(const bv_feasible_set_db_t* db, ivector_t* reasons_indices, bv_feasible_explain_mode_t mode, variable_t x) {

  // Sort variables by degree and trail level decreasing
  int_array_sort2(reasons_indices->data, reasons_indices->size, (void*) db, bv_feasible_set_compare_reasons);

  if (ctx_trace_enabled(db->ctx, "mcsat::bv::conflict")) {
    ctx_trace_printf(db->ctx, "filtering: before\n");
    print_conflict_reasons(ctx_trace_out(db->ctx), db, reasons_indices);
  }

  // Get term info
  term_t x_term = variable_db_get_term(db->ctx->var_db, x);
  uint32_t bitsize = bv_term_bitsize(db->ctx->terms, x_term);

  // Get value if needed
  const bvconstant_t* x_value = NULL;
  if (mode == EXPLAIN_ASSUMPTION) {
    const mcsat_value_t* x_value_mcsat = trail_get_value(db->ctx->trail, x);
    assert(x_value_mcsat->type == VALUE_BV);
    x_value = &x_value_mcsat->bv_value;

    if (ctx_trace_enabled(db->ctx, "mcsat::bv::conflict")) {
      ctx_trace_printf(db->ctx, "conflict var: ");
      ctx_trace_term(db->ctx, x_term);
      ctx_trace_printf(db->ctx, "conflict value: ");
      ctx_trace_value(db->ctx, x_value_mcsat);
      print_conflict_reasons(ctx_trace_out(db->ctx), db, reasons_indices);
    }
  }

  // Minimize the core
  ivector_t out;
  init_ivector(&out, 0);
  bdd_t bdd_true = bv_bdd_manager_true(db->bddm);
  bv_feasible_set_quickxplain(db, bdd_true, reasons_indices, 0, reasons_indices->size, &out, mode, x_term, x_value, bitsize);
  ivector_swap(reasons_indices, &out);
  delete_ivector(&out);

  // Sort again for consistency
  int_array_sort2(reasons_indices->data, reasons_indices->size, (void*) db, bv_feasible_set_compare_reasons);

  if (ctx_trace_enabled(db->ctx, "mcsat::bv::conflict")) {
    ctx_trace_printf(db->ctx, "filtering: after\n");
    print_conflict_reasons(ctx_trace_out(db->ctx), db, reasons_indices);
  }

}

void bv_feasible_set_db_get_reasons(const bv_feasible_set_db_t* db, variable_t x, ivector_t* reasons_out, ivector_t* lemma_reasons, bv_feasible_explain_mode_t mode) {

  ivector_t reasons_indices;
  init_ivector(&reasons_indices, 0);

  const variable_db_t* var_db = db->ctx->var_db;
  (void) var_db;

  // Get the indices of the set refinements
  bv_feasible_set_get_reason_indices(db, x, &reasons_indices);

  // Do a first pass filter from the back
  bv_feasible_set_filter_reason_indices(db, &reasons_indices, mode, x);

  // Return the conjunctive reasons
  uint32_t i;
  for (i = 0; i < reasons_indices.size; ++ i) {
    uint32_t set_index = reasons_indices.data[i];
    feasibility_list_element_t* element = db->memory + set_index;
    if (element->reasons_size == 1) {
      variable_t reason = element->reasons[0];
      assert(variable_db_is_boolean(var_db, reason));
      ivector_push(reasons_out, reason);
    } else {
      uint32_t j;
      for (j = 0; j < element->reasons_size; ++j) {
        variable_t reason = element->reasons[j];
        assert(variable_db_is_boolean(var_db, reason));
        ivector_push(lemma_reasons, reason);
      }
    }
  }

  delete_ivector(&reasons_indices);
}

void bv_feasible_set_db_gc_mark(bv_feasible_set_db_t* db, gc_info_t* gc_vars) {

  assert(db->ctx->trail->decision_level == db->ctx->trail->decision_level_base);

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

variable_t bv_feasible_set_db_get_fixed(bv_feasible_set_db_t* db) {
  for (; db->fixed_variables_i < db->fixed_variables.size; ++ db->fixed_variables_i) {
    variable_t var = db->fixed_variables.data[db->fixed_variables_i];
    if (!trail_has_value(db->ctx->trail, var)) {
      return var;
    }
  }
  return variable_null;
}
