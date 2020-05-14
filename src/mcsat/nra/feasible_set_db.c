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
 
#include "mcsat/nra/feasible_set_db.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/tracing.h"
#include "mcsat/nra/nra_plugin_internal.h"
#include "mcsat/nra/poly_constraint.h"

#include "utils/int_array_sort2.h"

#include <poly/feasibility_set.h>
#include <poly/upolynomial.h>

/**
 * Element in the list. Each element contains a pointer to the previous
 * version, the reason for the update (reason) and it's feasible set, and
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
  lp_feasibility_set_t* feasible_set;
  /** The feasible set of the reason (feasible = feasible intersect this) */
  lp_feasibility_set_t* reason_feasible_set;

} feasibility_list_element_t;

struct feasible_set_db_struct {

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

  /** BV context */
  plugin_context_t* ctx;
};

static
uint32_t feasible_set_db_get_index(feasible_set_db_t* db, variable_t x) {
  int_hmap_pair_t* find = int_hmap_find(&db->var_to_feasible_set_map, x);
  if (find == NULL) {
    return 0;
  } else {
    return find->val;
  }
}

void feasible_set_db_print_var(feasible_set_db_t* db, variable_t var, FILE* out) {
  fprintf(out, "Feasible sets of ");
  variable_db_print_variable(db->ctx->var_db, var, out);
  fprintf(out, " :\n");
  uint32_t index = feasible_set_db_get_index(db, var);
  while (index != 0) {
    feasibility_list_element_t* current = db->memory + index;
    fprintf(out, "\t");
    lp_feasibility_set_print(current->feasible_set, out);
    fprintf(out, "\n\t\t");
    lp_feasibility_set_print(current->reason_feasible_set, out);
    fprintf(out, "\n");
    if (current->reasons_size > 1) {
      fprintf(out, "\t\tDue to lemma\n");
    } else {
      fprintf(out, "\t\tDue to ");
      term_t reason_term = variable_db_get_term(db->ctx->var_db, current->reasons[0]);
      term_print_to_file(out, db->ctx->terms, reason_term);
      if (term_type_kind(db->ctx->terms, reason_term) == BOOL_TYPE) {
        // Otherwise it's a term evaluation, always true
        fprintf(out, " assigned to %s\n", trail_get_boolean_value(db->ctx->trail, current->reasons[0]) ? "true" : "false");
      }
    }
    index = current->prev;
  }
}

void feasible_set_db_print(feasible_set_db_t* db, FILE* out) {
  int_hmap_pair_t* it;
  for (it = int_hmap_first_record(&db->var_to_feasible_set_map); it != NULL; it = int_hmap_next_record(&db->var_to_feasible_set_map, it)) {

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
      lp_feasibility_set_print(db->memory[index].feasible_set, out);
      fprintf(out, "\n\t\t");
      lp_feasibility_set_print(db->memory[index].reason_feasible_set, out);
      fprintf(out, "\n");
      index = current->prev;
    }
  }
}

#define INITIAL_DB_SIZE 100

feasible_set_db_t* feasible_set_db_new(plugin_context_t* ctx) {
  feasible_set_db_t* db = safe_malloc(sizeof(feasible_set_db_t));

  db->memory_size = 1; // 0 is special null ref
  db->memory_capacity = INITIAL_DB_SIZE;
  db->memory = safe_malloc(sizeof(feasibility_list_element_t)*db->memory_capacity);

  init_int_hmap(&db->var_to_feasible_set_map, 0);
  init_ivector(&db->updates, 0);
  init_ivector(&db->fixed_variables, 0);

  db->fixed_variable_size = 0;
  db->fixed_variables_i = 0;

  db->updates_size = 0;

  scope_holder_construct(&db->scope);

  db->ctx = ctx;

  return db;
}

void feasible_set_db_delete(feasible_set_db_t* db) {
  // Delete the feasible sets
  uint32_t i;
  // Start from 1, 0 is special.
  for (i = 1; i < db->memory_size; ++ i) {
    safe_free(db->memory[i].reasons);
    lp_feasibility_set_t* s1 = db->memory[i].feasible_set;
    lp_feasibility_set_t* s2 = db->memory[i].reason_feasible_set;
    lp_feasibility_set_delete(s1);
    if (s1 != s2) {
      lp_feasibility_set_delete(s2);
    }
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

lp_feasibility_set_t* feasible_set_db_get(feasible_set_db_t* db, variable_t x) {
  uint32_t index = feasible_set_db_get_index(db, x);
  if (index == 0) {
    return NULL;
  } else {
    return db->memory[index].feasible_set;
  }
}

/** Update the feasible set of the variable with a new set */
bool feasible_set_db_update(feasible_set_db_t* db, variable_t x, lp_feasibility_set_t* new_set, variable_t* cstr_list, uint32_t cstr_count) {

  assert(db->updates_size == db->updates.size);

  bool feasible = true;

  if (ctx_trace_enabled(db->ctx, "nra::feasible_set_db")) {
    fprintf(ctx_trace_out(db->ctx), "feasible_set_db_update");
    feasible_set_db_print(db, ctx_trace_out(db->ctx));
  }

  // The one we're adding
  lp_feasibility_set_t* intersect = 0;

  // Intersect, if no difference, we're done
  const lp_feasibility_set_t* old_set = feasible_set_db_get(db, x);

  if (old_set != 0) {

    if (ctx_trace_enabled(db->ctx, "nra::feasible_set_db")) {
      ctx_trace_printf(db->ctx, "feasible_set_db_update()\n");
      ctx_trace_printf(db->ctx, "old_set = ");
      lp_feasibility_set_print(old_set, ctx_trace_out(db->ctx));
      ctx_trace_printf(db->ctx, "\nnew_set = ");
      lp_feasibility_set_print(new_set, ctx_trace_out(db->ctx));
      ctx_trace_printf(db->ctx, "\n");
    }

    assert(!lp_feasibility_set_is_empty(old_set));
    lp_feasibility_set_intersect_status_t status;
    intersect = lp_feasibility_set_intersect_with_status(old_set, new_set, &status);
    switch (status) {
    case LP_FEASIBILITY_SET_INTERSECT_S1:
      // Old set stays
      lp_feasibility_set_delete(intersect);
      lp_feasibility_set_delete(new_set);
      return true;
      break;
    case LP_FEASIBILITY_SET_INTERSECT_S2:
    case LP_FEASIBILITY_SET_NEW:
      // We have a proper new set
      break;
    case LP_FEASIBILITY_SET_EMPTY:
      // We have a new set, and we are infeasible
      feasible = false;
      break;
    }
  } else {
    // We don't have any info yet, this is the new one
    feasible = !lp_feasibility_set_is_empty(new_set);
    intersect = new_set;
  }

  // Get the previous
  uint32_t prev = feasible_set_db_get_index(db, x);

  // Allocate a new one
  uint32_t new_index = db->memory_size;
  // Allocate new element
  if (db->memory_size == db->memory_capacity) {
    db->memory_capacity = db->memory_capacity + db->memory_capacity/2;
    db->memory = safe_realloc(db->memory, db->memory_capacity*sizeof(feasibility_list_element_t));
  }
  db->memory_size ++;
  // Setup the element
  feasibility_list_element_t* new_element = db->memory + new_index;
  new_element->feasible_set = intersect;
  new_element->reason_feasible_set = new_set;
  new_element->prev = prev;
  // Reasons
  new_element->reasons_size = cstr_count;
  new_element->reasons = safe_malloc(sizeof(variable_t)*cstr_count);
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
  if (lp_feasibility_set_is_point(intersect)) {
    ivector_push(&db->fixed_variables, x);
    db->fixed_variable_size ++;
  }

  // Return whether we're feasible
  return feasible;
}

void feasible_set_db_push(feasible_set_db_t* db) {
  scope_holder_push(&db->scope,
     &db->updates_size,
     &db->fixed_variable_size,
     &db->fixed_variables_i,
     NULL
  );
}

void feasible_set_db_pop(feasible_set_db_t* db) {

  if (ctx_trace_enabled(db->ctx, "nra::feasible_set_db")) {
    fprintf(ctx_trace_out(db->ctx), "feasible_set_db_pop");
    feasible_set_db_print(db, ctx_trace_out(db->ctx));
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
    // Deallocate aloocated data
    lp_feasibility_set_t* s1 = element->feasible_set;
    lp_feasibility_set_t* s2 = element->reason_feasible_set;
    lp_feasibility_set_delete(s1);
    if (s1 != s2) {
      lp_feasibility_set_delete(s2);
    }
    safe_free(element->reasons);
    // Redirect map to the previous one
    int_hmap_pair_t* find = int_hmap_find(&db->var_to_feasible_set_map, x);
    assert(find != NULL);
    assert(find->val == db->memory_size);
    find->val = prev;
  }

  if (ctx_trace_enabled(db->ctx, "nra::feasible_set_db")) {
    feasible_set_db_print(db, ctx_trace_out(db->ctx));
  }
}

static
void feasible_set_get_conflict_reason_indices(feasible_set_db_t* db, variable_t x, ivector_t* reasons_indices) {
  // Go back from the top reason for x and gather the indices
  uint32_t reason_index = feasible_set_db_get_index(db, x);
  assert(reason_index);
  while (reason_index) {
    assert(reason_index);
    ivector_push(reasons_indices, reason_index);
    reason_index = db->memory[reason_index].prev;
  }
}

static
void feasible_set_quickxplain(const feasible_set_db_t* db, const lp_feasibility_set_t* current, ivector_t* reasons, uint32_t begin, uint32_t end, ivector_t* out) {

  uint32_t i;

  if (lp_feasibility_set_is_empty(current)) {
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
  lp_feasibility_set_t* feasible_A = lp_feasibility_set_new_copy(current);
  for (i = begin; i < begin + n; ++ i) {
    const lp_feasibility_set_t* feasible_i = db->memory[reasons->data[i]].reason_feasible_set;
    lp_feasibility_set_intersect_status_t intersect_status;
    lp_feasibility_set_t* intersect = lp_feasibility_set_intersect_with_status(feasible_A, feasible_i, &intersect_status);
    lp_feasibility_set_swap(intersect, feasible_A);
    lp_feasibility_set_delete(intersect);
  }
  uint32_t old_out_size = out->size;
  feasible_set_quickxplain(db, feasible_A, reasons, begin + n, end, out);
  lp_feasibility_set_delete(feasible_A);

  // Now, assert the minimized second half, and minimize the first half
  lp_feasibility_set_t* feasible_B = lp_feasibility_set_new_copy(current);
  for (i = old_out_size; i < out->size; ++ i) {
    const lp_feasibility_set_t* feasible_i = db->memory[out->data[i]].reason_feasible_set;
    lp_feasibility_set_intersect_status_t intersect_status;
    lp_feasibility_set_t* intersect = lp_feasibility_set_intersect_with_status(feasible_B, feasible_i, &intersect_status);
    lp_feasibility_set_swap(intersect, feasible_B);
    lp_feasibility_set_delete(intersect);
  }
  feasible_set_quickxplain(db, feasible_B, reasons, begin, begin + n, out);
  lp_feasibility_set_delete(feasible_B);
}

/** Compare variables first by degree, then by level, prefer non root constraints */
static
bool compare_reasons(void *nra_plugin, int32_t r1, int32_t r2) {

  uint32_t i;

  const nra_plugin_t* nra = (nra_plugin_t*) nra_plugin;
  feasible_set_db_t* db = nra->feasible_set_db;
  poly_constraint_db_t* poly_db = nra->constraint_db;
  const mcsat_trail_t* trail = nra->ctx->trail;

  // Get max degree and max level of the reasons of first constraint
  uint32_t r1_degree = 0;
  uint32_t r1_level = 0;
  for (i = 0; i < db->memory[r1].reasons_size; ++ i) {
    variable_t r1_i_var = db->memory[r1].reasons[i];
    if (trail_has_value(trail, r1_i_var)) {
      uint32_t r1_i_level = trail_get_level(trail, r1_i_var);
      if (r1_i_level > r1_level) {
        r1_level = r1_i_level;
      }
    }
    const poly_constraint_t* r1_i_constraint = poly_constraint_db_get(poly_db, r1_i_var);
    const lp_polynomial_t* r1_i_poly = poly_constraint_get_polynomial(r1_i_constraint);
    uint32_t r1_i_degree =  lp_polynomial_degree(r1_i_poly);
    if (r1_i_degree > r1_degree) {
      r1_degree = r1_i_degree;
    }
  }

  // Get max degree and max level of the reasons of second constraint
  uint32_t r2_degree = 0;
  uint32_t r2_level = 0;
  for (i = 0; i < db->memory[r2].reasons_size; ++ i) {
    variable_t r2_i_var = db->memory[r2].reasons[i];
    if (trail_has_value(trail, r2_i_var)) {
      uint32_t r2_i_level = trail_get_level(trail, r2_i_var);
      if (r2_i_level > r2_level) {
        r2_level = r2_i_level;
      }
    }
    const poly_constraint_t* r2_i_constraint = poly_constraint_db_get(poly_db, r2_i_var);
    const lp_polynomial_t* r2_i_poly = poly_constraint_get_polynomial(r2_i_constraint);
    uint32_t r2_i_degree =  lp_polynomial_degree(r2_i_poly);
    if (r2_i_degree > r2_degree) {
      r2_degree = r2_i_degree;
    }
  }

  // Prefer smaller degrees
  if (r1_degree != r2_degree) {
    return r1_degree < r2_degree;
  }

  // Otherwise take the one of lower level
  return r1_level < r2_level;
}

void print_conflict_reasons(FILE* out, feasible_set_db_t* db, nra_plugin_t* nra, ivector_t* reason_indices) {
  uint32_t i, j;
  poly_constraint_db_t* poly_db = nra->constraint_db;
  
  for (i = 0; i < reason_indices->size; ++ i) {
    fprintf(out, "[%d]: ", i);
    uint32_t r_i = reason_indices->data[i];
    uint32_t r_i_size = db->memory[r_i].reasons_size;
    for (j = 0; j < r_i_size; ++ j) {
      if (j) fprintf(out, ", ");
      variable_t r_i_var = db->memory[r_i].reasons[j];
      const poly_constraint_t* r_i_constraint = poly_constraint_db_get(poly_db, r_i_var);
      poly_constraint_print(r_i_constraint, out);
    }
    fprintf(out, "\n");                                               
  }
}

static
void feasible_set_filter_reason_indices(feasible_set_db_t* db, nra_plugin_t* nra, ivector_t* reasons_indices) {
  // The set we're trying to make empty
  lp_feasibility_set_t* S = lp_feasibility_set_new_full();

  // Sort variables by degree and trail level descreasing
  int_array_sort2(reasons_indices->data, reasons_indices->size, (void*) nra, compare_reasons);
 
  if (ctx_trace_enabled(db->ctx, "nra::conflict")) {
    ctx_trace_printf(db->ctx, "filtering: before\n");
    print_conflict_reasons(ctx_trace_out(db->ctx), db, nra, reasons_indices);
  }                           

  // Minimize the core
  ivector_t out;
  init_ivector(&out, 0);
  feasible_set_quickxplain(db, S, reasons_indices, 0, reasons_indices->size, &out);
  ivector_swap(reasons_indices, &out);
  delete_ivector(&out);

  // Sort again for consisency
  int_array_sort2(reasons_indices->data, reasons_indices->size, (void*) nra, compare_reasons);

  if (ctx_trace_enabled(db->ctx, "nra::conflict")) {
    ctx_trace_printf(db->ctx, "filtering: after\n");
    print_conflict_reasons(ctx_trace_out(db->ctx), db, nra, reasons_indices);
  }                           

  // Remove temps
  lp_feasibility_set_delete(S);
}

/**
 * Check if conflict without ignoring 0 indices.
 */
bool feasible_set_check_if_conflict(feasible_set_db_t* db, ivector_t* set_indices) {

  // The set we're trying to make empty
  lp_feasibility_set_t* S = lp_feasibility_set_new_full();

  // Go back from the top reason for x until empty interval is obtained
  uint32_t i;
  for (i = 0; i < set_indices->size; ++ i) {
    // Current reason we're considering
    uint32_t set_index = set_indices->data[i];
    if (set_index) {
      // Intersect with the current feasible set
      const lp_feasibility_set_t* reason_feasible = db->memory[set_index].reason_feasible_set;
      lp_feasibility_set_t* intersect = lp_feasibility_set_intersect(S, reason_feasible);

      if (ctx_trace_enabled(db->ctx, "nra::get_conflict")) {
        ctx_trace_printf(db->ctx, "S = "); lp_feasibility_set_print(S, ctx_trace_out(db->ctx)); ctx_trace_printf(db->ctx, "\n");
        ctx_trace_printf(db->ctx, "reason_feasible = "); lp_feasibility_set_print(reason_feasible, ctx_trace_out(db->ctx)); ctx_trace_printf(db->ctx, "\n");
        ctx_trace_printf(db->ctx, "intersect = "); lp_feasibility_set_print(intersect, ctx_trace_out(db->ctx)); ctx_trace_printf(db->ctx, "\n");
      }

      lp_feasibility_set_swap(intersect, S);
      lp_feasibility_set_delete(intersect);
    }
  }

  bool conflict = lp_feasibility_set_is_empty(S);

  // Remove temps
  lp_feasibility_set_delete(S);

  return conflict;
}

void feasible_set_db_get_conflict_reasons(feasible_set_db_t* db, nra_plugin_t* nra, variable_t x, ivector_t* reasons_out, ivector_t* lemma_reasons) {

  if (ctx_trace_enabled(db->ctx, "nra::get_conflict")) {
    ctx_trace_printf(db->ctx, "get_reasons of: ");
    variable_db_print_variable(db->ctx->var_db, x, ctx_trace_out(db->ctx));
    ctx_trace_printf(db->ctx, "\n");
  }

  ivector_t reasons_indices;
  init_ivector(&reasons_indices, 0);

  // Get the indices of the set refinements
  feasible_set_get_conflict_reason_indices(db, x, &reasons_indices);

  // Do a first pass filter from the back
  feasible_set_filter_reason_indices(db, nra, &reasons_indices);

  // Return the conjunctive reasons
  uint32_t i;
  for (i = 0; i < reasons_indices.size; ++ i) {
    uint32_t set_index = reasons_indices.data[i];
    feasibility_list_element_t* element = db->memory + set_index;
    if (element->reasons_size == 1) {
      variable_t reason = element->reasons[0];
      assert(variable_db_is_boolean(db->ctx->var_db, reason));
      ivector_push(reasons_out, reason);
    } else {
      uint32_t j;
      for (j = 0; j < element->reasons_size; ++j) {
        variable_t reason = element->reasons[j];
        assert(variable_db_is_boolean(db->ctx->var_db, reason));
        ivector_push(lemma_reasons, reason);
      }
    }
  }

  delete_ivector(&reasons_indices);
}

variable_t feasible_set_db_get_cheap_unassigned(feasible_set_db_t* db, lp_value_t* value) {

  variable_t best_var = variable_null;
  size_t best_var_degree = 0;
  if (ctx_trace_enabled(db->ctx, "nra::decide")) {
    feasible_set_db_print(db, ctx_trace_out(db->ctx));
  }

  int_hmap_pair_t* it = int_hmap_first_record(&db->var_to_feasible_set_map);
  for (; it != NULL; it = int_hmap_next_record(&db->var_to_feasible_set_map, it)) {
    variable_t current_var = it->key;
    if (!trail_has_value(db->ctx->trail, current_var)) {
      lp_feasibility_set_t* current_var_set = feasible_set_db_get(db, current_var);
      if (current_var_set == NULL) {
        if (best_var == variable_null || db->ctx->cmp_variables(db->ctx, current_var, best_var)) {
          best_var = current_var;
          best_var_degree = 0;
        }
      } else {
        lp_feasibility_set_pick_value(current_var_set, value);
        if (lp_value_is_rational(value)) {
          if (best_var == variable_null || db->ctx->cmp_variables(db->ctx, current_var, best_var)) {
            best_var = current_var;
            best_var_degree = 0;
          }
        } else {
          size_t x_degree = lp_upolynomial_degree(value->value.a.f);
          if (best_var == variable_null || x_degree < best_var_degree) {
            best_var = current_var;
            best_var_degree = x_degree;
          } else if (x_degree == best_var_degree) {

          }
        }
      }
    }
  }

  assert(best_var != variable_null);
  lp_feasibility_set_t* best_var_set = feasible_set_db_get(db, best_var);
  if (best_var_set) {
    lp_feasibility_set_pick_value(best_var_set, value);
  } else {
    lp_value_assign_zero(value);
  }

  return best_var;
}

void feasible_set_db_gc_mark(feasible_set_db_t* db, gc_info_t* gc_vars) {

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

variable_t feasible_set_db_get_fixed(feasible_set_db_t* db) {
  for (; db->fixed_variables_i < db->fixed_variables.size; ++ db->fixed_variables_i) {
    variable_t var = db->fixed_variables.data[db->fixed_variables_i];
    if (!trail_has_value(db->ctx->trail, var)) {
      return var;
    }
  }
  return variable_null;
}

void feasible_set_db_approximate_value(feasible_set_db_t* db, variable_t constraint_var, lp_interval_t* result) {
  lp_feasibility_set_t* feasible = feasible_set_db_get(db, constraint_var);
  if (feasible != NULL) {
    lp_feasibility_set_to_interval(feasible, result);
  } else {
    lp_interval_t full;
    lp_interval_construct_full(&full);
    lp_interval_swap(&full, result);
    lp_interval_destruct(&full);
  }
}
