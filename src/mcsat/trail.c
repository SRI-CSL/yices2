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
 
#include "mcsat/trail.h"
#include "io/term_printer.h"
#include "io/yices_pp.h"

void trail_construct(mcsat_trail_t* trail, const variable_db_t* var_db) {
  trail->var_db = var_db;
  init_ivector(&trail->elements, 0);
  init_ivector(&trail->to_repropagate, 0);
  init_ivector(&trail->level_sizes, 0);
  trail->decision_level = 0;
  trail->decision_level_base = 0;
  mcsat_model_construct(&trail->model);
  init_ivector(&trail->type, 0);
  init_ivector(&trail->level, 0);
  init_ivector(&trail->index, 0);
  init_ivector(&trail->id, 0);
  init_ivector(&trail->unassigned, 0);
  trail->inconsistent = false;
}

static inline
void init_ivector_copy(ivector_t* v, const ivector_t* from) {
  init_ivector(v, from->size);
  ivector_add(v, from->data, from->size);
}

void trail_construct_copy(mcsat_trail_t* trail, const mcsat_trail_t* from) {
  trail->var_db = from->var_db;
  init_ivector_copy(&trail->elements, &from->elements);
  init_ivector_copy(&trail->to_repropagate, &from->to_repropagate);
  init_ivector_copy(&trail->level_sizes, &from->level_sizes);
  trail->decision_level = from->decision_level;
  trail->decision_level_base = from->decision_level_base;
  mcsat_model_construct_copy(&trail->model, &from->model);
  init_ivector_copy(&trail->type, &from->type);
  init_ivector_copy(&trail->level, &from->level);
  init_ivector_copy(&trail->index, &from->index);
  init_ivector_copy(&trail->id, &from->id);
  init_ivector_copy(&trail->unassigned, &from->unassigned);
  trail->inconsistent = from->inconsistent;
}

void trail_destruct(mcsat_trail_t* trail) {
  trail->var_db = NULL;
  delete_ivector(&trail->elements);
  delete_ivector(&trail->to_repropagate);
  delete_ivector(&trail->level_sizes);
  trail->decision_level = 0;
  mcsat_model_destruct(&trail->model);
  delete_ivector(&trail->type);
  delete_ivector(&trail->level);
  delete_ivector(&trail->index);
  delete_ivector(&trail->id);
  delete_ivector(&trail->unassigned);
}

void trail_new_variable_notify(mcsat_trail_t* trail, variable_t x) {
  // Notify the model
  mcsat_model_new_variable_notify(&trail->model, x);
  // Resize variable info
  while (trail->type.size <= x) {
    ivector_push(&trail->type, UNASSIGNED);
    ivector_push(&trail->level, -1);
    ivector_push(&trail->index, -1);
    ivector_push(&trail->id, -1);
  }
}

void trail_print(const mcsat_trail_t* trail, FILE* out) {
  uint32_t i;
  variable_t var;
  assignment_type_t var_type;

  fprintf(out, "[\n");
  for (i = 0; i < trail->elements.size; ++ i) {
    if (i) {
      fprintf(out, ", ");
    }
    var = trail->elements.data[i];
    var_type = trail_get_assignment_type(trail, var);

    if (var_type == DECISION) {
      fprintf(out, "\n");
    } else if (i > 0) {
      variable_t prev_var = trail->elements.data[i-1];
      uint32_t l = trail_get_level(trail, prev_var);
      uint32_t l_end = trail_get_level(trail, var);
      for (; l < l_end; ++ l) {
        fprintf(out, "\n ----------- PUSH -------------- \n");
      }
    }

    variable_db_print_variable(trail->var_db, var, out);

    switch (var_type) {
    case DECISION:
      fprintf(out, " *= ");
      break;
    case PROPAGATION:
      fprintf(out, " == ");
      break;
    default:
      assert(false);
    }
    mcsat_value_print(trail->model.values + var, out);
  }
  fprintf(out, "\n]\n");
}

static inline
void trail_new_decision(mcsat_trail_t* trail) {
  assert(trail_is_consistent(trail));
  trail->decision_level ++;
  ivector_push(&trail->level_sizes, trail->elements.size);
}

void trail_new_base_level(mcsat_trail_t* trail) {
  assert(trail->decision_level == trail->decision_level_base);
  trail_new_decision(trail);
  trail->decision_level_base = trail->decision_level;
}

uint32_t trail_pop_base_level(mcsat_trail_t* trail) {
  assert(trail->decision_level == trail->decision_level_base);
  assert(trail->decision_level_base > 0);
  trail->decision_level_base --;
  return trail->decision_level_base;
}

static inline
void trail_undo_decision(mcsat_trail_t* trail) {
  trail->decision_level --;
  ivector_pop(&trail->level_sizes);
}

static inline
void trail_set_value(mcsat_trail_t* trail, variable_t x, const mcsat_value_t* value, uint32_t id, assignment_type_t type, uint32_t level) {
  assert(trail->index.data[x] == -1);
  assert(trail->type.data[x] == UNASSIGNED);
  assert(trail->level.data[x] == -1);
  assert(trail->id.data[x] == -1);
  assert((type == DECISION && level == trail->decision_level) || (type == PROPAGATION && level <= trail->decision_level));

  // Remember the index
  trail->index.data[x] = trail->elements.size;
  // Set the type
  trail->type.data[x] = type;
  // Set the level
  trail->level.data[x] = level;
  // Set the id of the decision
  trail->id.data[x] = id;

  // Set the value
  assert(value->type != VALUE_BOOLEAN || variable_db_is_boolean(trail->var_db, x));
  mcsat_model_set_value(&trail->model, x, value);
}

static inline
void trail_undo_value(mcsat_trail_t* trail, variable_t x) {
  trail->type.data[x] = UNASSIGNED;
  trail->index.data[x] = -1;
  trail->level.data[x] = -1;
  trail->id.data[x] = -1;
  ivector_push(&trail->unassigned, x);
}

void trail_add_decision(mcsat_trail_t* trail, variable_t x, const mcsat_value_t* value, uint32_t id) {
  assert(x >= 0);
  assert(!trail_has_value(trail, x));

  // Mark new decision
  trail_new_decision(trail);
  // Set the value
  trail_set_value(trail, x, value, id, DECISION, trail->decision_level);
  // Push the element
  ivector_push(&trail->elements, x);
}

void trail_pop_decision(mcsat_trail_t* trail) {
  variable_t x;
  // Undo the value with the addition of decision unmark
  x = ivector_last(&trail->elements);
  trail_undo_value(trail, x);
  // Don't unset value, keep for caching: mcsat_model_unset_value(&trail->model, x);
  trail_undo_decision(trail);
  ivector_pop(&trail->elements);
  // Also, we're back into consistent
  trail->inconsistent = false;
  // Repropagate
  while (trail->to_repropagate.size > 0) {
    x = ivector_last(&trail->to_repropagate);
    ivector_pop(&trail->to_repropagate);
    trail->index.data[x] = trail->elements.size;
    ivector_push(&trail->elements, x);
  }
}

void trail_add_propagation(mcsat_trail_t* trail, variable_t x, const mcsat_value_t* value, uint32_t id, uint32_t level) {
  assert(x >= 0);
  assert(!trail_has_value(trail, x));
  assert(level >= trail->decision_level_base);
  // Set the value
  trail_set_value(trail, x, value, id, PROPAGATION, level);
  // Push the element
  ivector_push(&trail->elements, x);
}


void trail_pop_propagation(mcsat_trail_t* trail) {
  variable_t x;
  uint32_t x_level;
  // Undo the value with the addition of decision unmark
  x = ivector_last(&trail->elements);
  x_level = trail_get_level(trail, x);
  if (x_level == trail->decision_level) {
    trail_undo_value(trail, x);
    // Don't unset model value, keep for caching: mcsat_model_unset_value(&trail->model, x);
  } else {
    // Propagations at lower levels, remember and re-propagate during on pop-decision
    assert(x_level < trail->decision_level);
    ivector_push(&trail->to_repropagate, x);
  }
  ivector_pop(&trail->elements);
}

void trail_pop(mcsat_trail_t* trail) {
  assert(trail->decision_level >= trail->decision_level_base);
  assert(trail->level_sizes.size > 0);
  uint32_t target_size = ivector_last(&trail->level_sizes);
  while (trail->elements.size > target_size && trail_get_assignment_type(trail, trail_back(trail)) != DECISION) {
    trail_pop_propagation(trail);
  };
  if (trail->elements.size > target_size) {
    trail_pop_decision(trail);
  } else {
    // Fake push, no decision, so we just undo
    trail_undo_decision(trail);
    // Also, we're back into consistent
    trail->inconsistent = false;
  }
}

void trail_gc_mark(mcsat_trail_t* trail, gc_info_t* gc_vars) {

  uint32_t i;
  variable_t var;

  assert(trail->to_repropagate.size == 0);
  assert(trail->unassigned.size == 0);
  assert(trail->decision_level == trail->decision_level_base);

  for (i = 0; i < trail->elements.size; ++ i) {
    var = trail->elements.data[i];
    assert(variable_db_is_variable(trail->var_db, var, true));
    gc_info_mark(gc_vars, var);
  }
}

void trail_gc_sweep(mcsat_trail_t* trail, const gc_info_t* gc_vars) {
  variable_t var;

  assert(gc_vars->is_id);

  // Remove from the model cache, otherwise the cache might contain wrongly
  // typed variables
  for (var = 0; var < trail->model.size; ++ var) {
    if (var != variable_null && gc_info_get_reloc(gc_vars, var) == variable_null) {
      assert(!trail_has_value(trail, var));
      if (mcsat_model_has_value(&trail->model, var)) {
        mcsat_model_unset_value(&trail->model, var);
      }
      assert(!trail_has_value(trail, var));
    }
  }
}
