/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "mcsat/uf/uf_feasible_set_db.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/tracing.h"

#include "utils/int_array_sort.h"

#include "yices.h"

/**
 * Element in the list. Each element contains a pointer to the previous
 * version, the reason for the update/
 */
typedef struct {
  /** Next element */
  uint32_t prev;
  /** Is it an equality */
  bool eq;
  /** The value (x != value) or (x = value) */
  uint32_t value;
  /** Reasons for the update. */
  variable_t reason;
} uf_feasible_list_element_t;

struct uf_feasible_set_db_struct {

  /** Elements of the lists */
  uf_feasible_list_element_t* memory;

  /** The currently occupied memory size */
  uint32_t memory_size;

  /** The capacity of the memory */
  uint32_t memory_capacity;

  /** Map from variables to the first element (current feasible set) */
  int_hmap_t var_to_eq_set_map;

  /** Variables that were updated, so we can backtrack */
  ivector_t updates;

  /** All variables that were fixed */
  ivector_t fixed_variables;

  /** Index into the fixed variables */
  uint32_t fixed_variables_i;

  /** Scope for push/pop */
  scope_holder_t scope;

  /** Trail */
  const mcsat_trail_t* trail;

  /** Variable database */
  variable_db_t* var_db;

  /** Terms */
  term_table_t* terms;
};

static
uint32_t uf_feasible_set_db_get_index(uf_feasible_set_db_t* db, variable_t x) {
  int_hmap_pair_t* find = int_hmap_find(&db->var_to_eq_set_map, x);
  if (find == NULL) {
    return 0;
  } else {
    return find->val;
  }
}

void uf_feasible_set_db_print_var(uf_feasible_set_db_t* db, variable_t var, FILE* out) {
  fprintf(out, "Feasible sets of ");
  variable_db_print_variable(db->var_db, var, out);
  fprintf(out, " :\n");
  uint32_t index = uf_feasible_set_db_get_index(db, var);
  while (index != 0) {
    uf_feasible_list_element_t* current = db->memory + index;
    fprintf(out, "\t%d\n", current->value);
    fprintf(out, "\t\tDue to ");
    term_t reason_term = variable_db_get_term(db->var_db, current->reason);
    term_print_to_file(out, db->terms, reason_term);
    if (term_type_kind(db->terms, reason_term) == BOOL_TYPE) {
      // Otherwise it's a term evaluation, always true
      fprintf(out, " assigned to %s\n", trail_get_boolean_value(db->trail, current->reason) ? "true" : "false");
    }
    index = current->prev;
  }
}

void uf_feasible_set_db_print(uf_feasible_set_db_t* db, FILE* out) {
  int_hmap_pair_t* it;
  for (it = int_hmap_first_record(&db->var_to_eq_set_map); it != NULL; it = int_hmap_next_record(&db->var_to_eq_set_map, it)) {

    variable_t var = it->key;
    fprintf(out, "Feasible sets of ");
    variable_db_print_variable(db->var_db, var, out);
    fprintf(out, " :\n");
    if (trail_has_value(db->trail, var)) {
      fprintf(out, "\tassigned to: ");
      const mcsat_value_t* var_value = trail_get_value(db->trail, var);
      mcsat_value_print(var_value, out);
      fprintf(out, "\n");
    }

    uf_feasible_set_db_print_var(db, var, out);
  }
}

#define INITIAL_DB_SIZE 100

uf_feasible_set_db_t* uf_feasible_set_db_new(term_table_t* terms, variable_db_t* var_db, const mcsat_trail_t* trail) {
  uf_feasible_set_db_t* db = safe_malloc(sizeof(uf_feasible_set_db_t));

  db->memory_size = 1; // 0 is special null ref
  db->memory_capacity = INITIAL_DB_SIZE;
  db->memory = safe_malloc(sizeof(uf_feasible_list_element_t)*db->memory_capacity);

  init_int_hmap(&db->var_to_eq_set_map, 0);
  init_ivector(&db->updates, 0);
  init_ivector(&db->fixed_variables, 0);

  db->fixed_variables_i = 0;

  scope_holder_construct(&db->scope);

  db->trail = trail;
  db->var_db = var_db;
  db->terms = terms;

  return db;
}

void uf_feasible_set_db_delete(uf_feasible_set_db_t* db) {
  // Delete
  delete_int_hmap(&db->var_to_eq_set_map);
  delete_ivector(&db->updates);
  delete_ivector(&db->fixed_variables);
  scope_holder_destruct(&db->scope);
  // Free the memory
  safe_free(db->memory);
  safe_free(db);
}

uint32_t uf_feasible_set_db_get(uf_feasible_set_db_t* db, variable_t x) {
  uint32_t index = uf_feasible_set_db_get_index(db, x);

  // If no constraints, just return 0
  if (index == 0) {
    return 0;
  }

  // Check if top one is equality
  uf_feasible_list_element_t* current = db->memory + index;
  if (current->eq) {
    return current->value;
  }

  // Just dis-equalities, pick the smallest available one
  ivector_t disequal_values;
  init_ivector(&disequal_values, 0);

  while (index != 0) {
    current = db->memory + index;
    assert(!current->eq);
    ivector_push(&disequal_values, current->value);
    index = current->prev;
  }

  int_array_sort(disequal_values.data, disequal_values.size);

  uint32_t value = 0;
  uint32_t i = 0;
  while (i < disequal_values.size && value == disequal_values.data[i]) {
    value ++;
    i ++;
  }

  delete_ivector(&disequal_values);

  return value;
}

static
void uf_feasible_set_new_element(uf_feasible_set_db_t* db, variable_t x, bool eq, uint32_t value, variable_t reason) {
  // Allocate a new one
  uint32_t old_index = uf_feasible_set_db_get_index(db, x);
  uint32_t new_index = db->memory_size;
  // Allocate new element
  if (db->memory_size == db->memory_capacity) {
    db->memory_capacity = db->memory_capacity + db->memory_capacity/2;
    db->memory = safe_realloc(db->memory, db->memory_capacity*sizeof(uf_feasible_list_element_t));
  }
  db->memory_size ++;
  // Setup the element
  uf_feasible_list_element_t* new_element = db->memory + new_index;
  new_element->eq = eq;
  new_element->reason = reason;
  new_element->value = value;
  new_element->prev = old_index;
  // Add to map
  int_hmap_pair_t* find = int_hmap_find(&db->var_to_eq_set_map, x);
  if (find == NULL) {
    int_hmap_add(&db->var_to_eq_set_map, x, new_index);
  } else {
    find->val = new_index;
  }
  // Add to updates list
  ivector_push(&db->updates, x);

  // If fixed, put into the fixed array
  if (eq) {
    ivector_push(&db->fixed_variables, x);
  }
}

bool uf_feasible_set_db_set_disequal(uf_feasible_set_db_t* db, variable_t x, uint32_t v, variable_t reason) {
  uint32_t index = uf_feasible_set_db_get_index(db, x);

  bool conflict = false;

  while (index != 0) {
    uf_feasible_list_element_t* current = db->memory + index;
    if (current->eq) {
      // We're set to be equal already
      if (v == current->value) {
        conflict = true;
        break;
      } else {
        // No new information
        return true;
      }
    } else {
      // We know this already
      if (v == current->value) {
        return true;
      }
    }
    index = current->prev;
  }

  // New information, record it
  uf_feasible_set_new_element(db, x, false, v, reason);

  return !conflict;
}

bool uf_feasible_set_db_set_equal(uf_feasible_set_db_t* db, variable_t x, uint32_t v, variable_t reason) {
  uint32_t index = uf_feasible_set_db_get_index(db, x);

  bool conflict = false;

  while (index != 0) {
    uf_feasible_list_element_t* current = db->memory + index;
    if (current->eq) {
      // We're set to be equal already
      if (v == current->value) {
        // No new information
        return true;
      } else {
        // We have a conflict
        conflict = true;
        break;
      }
    } else {
      // Just check for conflicts
      if (v == current->value) {
        conflict = true;
        break;
      }
    }
    index = current->prev;
  }

  // New information, record it
  uf_feasible_set_new_element(db, x, true, v, reason);

  return !conflict;
}

void uf_feasible_set_db_push(uf_feasible_set_db_t* db) {
  scope_holder_push(&db->scope,
     &db->updates.size,
     &db->fixed_variables.size,
     &db->fixed_variables_i,
     NULL
  );
}

void uf_feasible_set_db_pop(uf_feasible_set_db_t* db) {

  uint32_t old_updates_size;
  uint32_t old_fixed_variable_size;

  scope_holder_pop(&db->scope,
      &old_updates_size,
      &old_fixed_variable_size,
      &db->fixed_variables_i,
      NULL
  );

  // Undo fixed variables
  ivector_shrink(&db->fixed_variables, old_fixed_variable_size);

  // Undo updates
  while (db->updates.size > old_updates_size) {
    // The variable that was updated
    variable_t x = ivector_last(&db->updates);
    ivector_pop(&db->updates);
    // Remove the element
    db->memory_size --;
    uf_feasible_list_element_t* element = db->memory + db->memory_size;
    uint32_t prev = element->prev;
    // Redirect map to the previous one
    int_hmap_pair_t* find = int_hmap_find(&db->var_to_eq_set_map, x);
    assert(find != NULL);
    assert(find->val == db->memory_size);
    find->val = prev;
  }

}

variable_t uf_feasible_set_db_get_eq_reason(uf_feasible_set_db_t* db, variable_t x) {

  // Go back from the top reason for x and gather the indices
  uint32_t index = uf_feasible_set_db_get_index(db, x);
  assert(index);

  assert(index);
  while (index) {
    uf_feasible_list_element_t* current = db->memory + index;
    if (current->eq) {
      return current->reason;
    }
    index = current->prev;
  }

  assert(false);
  return variable_null;
}

void uf_feasible_set_db_get_conflict(uf_feasible_set_db_t* db, variable_t x, ivector_t* conflict) {
  // Go back from the top reason for x and gather the indices
  uint32_t index = uf_feasible_set_db_get_index(db, x);
  assert(index);

  // Conflict is always between top one and one some below
  uf_feasible_list_element_t* first = db->memory + index;

  uf_feasible_list_element_t* current = NULL;

  index = first->prev;
  assert(index);
  while (index) {

    current = db->memory + index;

    if (first->eq && current->eq) {
      // Second equality must be in conflict.
      // We have x = y && x = z, implying different values on x
      // Conflict is x = y && x = z && y != z
      assert(first->value != current->value);

      variable_t x_eq_y_var = first->reason;
      variable_t x_eq_z_var = current->reason;
      assert(trail_get_boolean_value(db->trail, x_eq_y_var));
      assert(trail_get_boolean_value(db->trail, x_eq_z_var));
      term_t x_eq_y = variable_db_get_term(db->var_db, x_eq_y_var);
      term_t x_eq_z = variable_db_get_term(db->var_db, x_eq_z_var);
      composite_term_t* x_eq_y_desc = eq_term_desc(db->terms, x_eq_y);
      composite_term_t* x_eq_z_desc = eq_term_desc(db->terms, x_eq_z);

      term_t x_term = variable_db_get_term(db->var_db, x);
      term_t y_term = x_eq_y_desc->arg[0] == x_term ? x_eq_y_desc->arg[1] : x_eq_y_desc->arg[0];
      term_t z_term = x_eq_z_desc->arg[0] == x_term ? x_eq_z_desc->arg[1] : x_eq_z_desc->arg[0];
      term_t y_eq_z = yices_eq(y_term, z_term);

      ivector_push(conflict, x_eq_y);
      ivector_push(conflict, x_eq_z);
      ivector_push(conflict, opposite_term(y_eq_z));

      return;
    }

    if (first->eq && !current->eq) {
      if (first->value == current->value) {
        // We have x = y && x != z, the conflict being
        // x = y && x != z && y = z

        variable_t x_eq_y_var = first->reason;
        variable_t x_eq_z_var = current->reason;
        assert(trail_get_boolean_value(db->trail, x_eq_y_var));
        assert(!trail_get_boolean_value(db->trail, x_eq_z_var));
        term_t x_eq_y = variable_db_get_term(db->var_db, x_eq_y_var);
        term_t x_eq_z = variable_db_get_term(db->var_db, x_eq_z_var);
        composite_term_t* x_eq_y_desc = eq_term_desc(db->terms, x_eq_y);
        composite_term_t* x_eq_z_desc = eq_term_desc(db->terms, x_eq_z);

        term_t x_term = variable_db_get_term(db->var_db, x);
        term_t y_term = x_eq_y_desc->arg[0] == x_term ? x_eq_y_desc->arg[1] : x_eq_y_desc->arg[0];
        term_t z_term = x_eq_z_desc->arg[0] == x_term ? x_eq_z_desc->arg[1] : x_eq_z_desc->arg[0];
        term_t y_eq_z = yices_eq(y_term, z_term);

        ivector_push(conflict, x_eq_y);
        ivector_push(conflict, opposite_term(x_eq_z));
        ivector_push(conflict, y_eq_z);

        return;
      }
    }

    if (!first->eq && current->eq) {
      // Equality: must be in conflict
      assert(first->value == current->value);

      // We have x != y && x = z, the conflict being
      // x != y && x = z && y = z

      variable_t x_eq_y_var = first->reason;
      variable_t x_eq_z_var = current->reason;
      assert(!trail_get_boolean_value(db->trail, x_eq_y_var));
      assert(trail_get_boolean_value(db->trail, x_eq_z_var));
      term_t x_eq_y = variable_db_get_term(db->var_db, x_eq_y_var);
      term_t x_eq_z = variable_db_get_term(db->var_db, x_eq_z_var);
      composite_term_t* x_eq_y_desc = eq_term_desc(db->terms, x_eq_y);
      composite_term_t* x_eq_z_desc = eq_term_desc(db->terms, x_eq_z);

      term_t x_term = variable_db_get_term(db->var_db, x);
      term_t y_term = x_eq_y_desc->arg[0] == x_term ? x_eq_y_desc->arg[1] : x_eq_y_desc->arg[0];
      term_t z_term = x_eq_z_desc->arg[0] == x_term ? x_eq_z_desc->arg[1] : x_eq_z_desc->arg[0];
      term_t y_eq_z = yices_eq(y_term, z_term);

      ivector_push(conflict, opposite_term(x_eq_y));
      ivector_push(conflict, x_eq_z);
      ivector_push(conflict, y_eq_z);

      return;
    }

    index = db->memory[index].prev;
  }

  assert(false);
}

void uf_feasible_set_db_gc_mark(uf_feasible_set_db_t* db, gc_info_t* gc_vars) {

  assert(db->trail->decision_level == 0);

  if (gc_vars->level == 0) {
    // We keep all the reasons (start from 1, 0 is not used)
    uint32_t element_i;
    for (element_i = 1; element_i < db->memory_size; ++ element_i) {
      uf_feasible_list_element_t* element = db->memory + element_i;
      gc_info_mark(gc_vars, element->reason);
    }
  }
}

void uf_feasible_set_db_gc_sweep(uf_feasible_set_db_t* db, const gc_info_t* gc_vars) {
  // We relocatre all reasons
  uint32_t element_i;
  for (element_i = 1; element_i < db->memory_size; ++ element_i) {
    uf_feasible_list_element_t* element = db->memory + element_i;
    variable_t x = element->reason;
    x = gc_info_get_reloc(gc_vars, x);
    assert(x != variable_null);
    element->reason = x;
  }
}



variable_t uf_feasible_set_db_get_fixed(uf_feasible_set_db_t* db) {
  for (; db->fixed_variables_i < db->fixed_variables.size; ++ db->fixed_variables_i) {
    variable_t var = db->fixed_variables.data[db->fixed_variables_i];
    if (!trail_has_value(db->trail, var)) {
      return var;
    }
  }
  return variable_null;
}
