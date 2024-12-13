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
 
#ifndef MCSAT_TRAIL_H_
#define MCSAT_TRAIL_H_

#include "mcsat/variable_db.h"
#include "mcsat/model.h"
#include "mcsat/mcsat_types.h"
#include "mcsat/gc.h"

typedef enum {
  /** A decided value */
  DECISION,
  /** A propagated value */
  PROPAGATION,
  /** No value */
  UNASSIGNED
} assignment_type_t;

/*
 * Trail of the solver containing all information that the plugins need to
 * reason. It contains:
 * - the trail itself, i.e. the sequence of variable assignments,
 * - the model, so that plugins can query the values of variables, and
 * - information about the levels of variables (so that plugins can compute
 *   propagation levels).
 */
struct mcsat_trail_s {

  /** The variable database */
  const variable_db_t* var_db;

  /** Trail elements */
  ivector_t elements;

  /** The elements to repropagate */
  ivector_t to_repropagate;

  /** Trail containing trail sizes per decision level */
  ivector_t level_sizes;

  /** Decision level */
  uint32_t decision_level;

  /** Base decision level */
  uint32_t decision_level_base;

  /** The values per variable */
  mcsat_model_t model;

  /** Type of the assignment per variable (assignment_type_t) */
  ivector_t type;

  /** Levels per variable (-1) for unassigned */
  ivector_t level;

  /** Index per variable (-1) for unassigned */
  ivector_t index;

  /** Id of the source of the value */
  ivector_t id;

  /** List of unassigned variables */
  ivector_t unassigned;

  /** Are we in conflict */
  bool inconsistent;

};

/**
 * Construct a given trail. Each value constructed must not exceed the given
 * size.
 */
void trail_construct(mcsat_trail_t* trail, const variable_db_t* var_db);

/** Copy contruct */
void trail_construct_copy(mcsat_trail_t* trail, const mcsat_trail_t* from);

/** Destruct a given trail */
void trail_destruct(mcsat_trail_t* trail);

/** Called on notifications of new variables. */
void trail_new_variable_notify(mcsat_trail_t* trail, variable_t x);

/** Get the size of the trail */
static inline
uint32_t trail_size(const mcsat_trail_t* trail) {
  return trail->elements.size;
}

/** Is the trail consistent (no inconsistent propagation) */
static inline
bool trail_is_consistent(const mcsat_trail_t* trail) {
  return !trail->inconsistent;
}

/** Set the trail inconsistent */
static inline
void trail_set_inconsistent(mcsat_trail_t* trail) {
  trail->inconsistent = true;
}

/** Get the trail element at given position */
static inline
variable_t trail_at(const mcsat_trail_t* trail, uint32_t i) {
  assert(i < trail->elements.size);
  return trail->elements.data[i];
}

/** Get the last element of the trail */
static inline
variable_t trail_back(const mcsat_trail_t* trail) {
  assert(trail->elements.size > 0);
  return trail->elements.data[trail->elements.size - 1];
}

/** Print the trail to the output */
void trail_print(const mcsat_trail_t* trail, FILE* out);

/** Get the level of an assigned variable */
static inline
uint32_t trail_get_level(const mcsat_trail_t* trail, variable_t var) {
  assert(var < trail->level.size);
  assert(trail->level.data[var] >= 0);
  return trail->level.data[var];
}

/** Get the index of an assigned variable in the trail */
static inline
uint32_t trail_get_index(const mcsat_trail_t* trail, variable_t var) {
  assert(var < trail->index.size);
  assert(trail->index.data[var] >= 0);
  return trail->index.data[var];
}

/**
 * Returns true if the value of var is set. We check this by checking the level
 * of the variable. The value itself is kept so that we can use it for caching.
 */
static inline
bool trail_has_value(const mcsat_trail_t* trail, variable_t var) {
  assert(var < trail->level.size);
  bool has_value = (trail->level.data[var] >= 0);
  assert(!has_value || mcsat_model_get_value(&trail->model, var)->type != VALUE_NONE);
  return has_value;
}

/** Returns true if the variable has a cached value other than NONE */
static inline
bool trail_has_cached_value(const mcsat_trail_t* trail, variable_t var) {
  assert(var < trail->model.size);
  return mcsat_model_get_value(&trail->model, var)->type != VALUE_NONE;
}

/** Returns true if the value of var is other than NONE at base level */
static inline
bool trail_has_value_at_base(const mcsat_trail_t* trail, variable_t var) {
  assert(var < trail->model.size);
  assert(var < trail->level.size);
  return trail->level.data[var] >= 0 && trail->level.data[var] <= trail->decision_level_base;
}

/** Returns true if the trail is at base level */
static inline
bool trail_is_at_base_level(const mcsat_trail_t* trail) {
  return trail->decision_level == trail->decision_level_base;
}

/** Set the trail base level to current decision level */
void trail_new_base_level(mcsat_trail_t* trail);

/** Pop the base level down, returns the new base level (current-1) */
uint32_t trail_pop_base_level(mcsat_trail_t* trail);

/** Get the value of the variable */
static inline
const mcsat_value_t* trail_get_value(const mcsat_trail_t* trail, variable_t var) {
  assert(trail_has_value(trail, var));
  return mcsat_model_get_value(&trail->model, var);
}

/** Get the cached value of the variable */
static inline
const mcsat_value_t* trail_get_cached_value(const mcsat_trail_t* trail, variable_t var) {
  assert(!trail_has_value(trail, var));
  return mcsat_model_get_value(&trail->model, var);
}

/** Get the value timestamp of the variable */
static inline
uint32_t trail_get_value_timestamp(const mcsat_trail_t* trail, variable_t var) {
  assert(trail_has_value(trail, var));
  return mcsat_model_get_value_timestamp(&trail->model, var);
}


/** Get the boolean value of the variable */
static inline
bool trail_get_boolean_value(const mcsat_trail_t* trail, variable_t var) {
  const mcsat_value_t* value = trail_get_value(trail, var);
  assert(value->type == VALUE_BOOLEAN);
  return value->b;
}

/** Add a new decision x -> value */
void trail_add_decision(mcsat_trail_t* trail, variable_t x, const mcsat_value_t* value, uint32_t id);

/** Add a new propagation x -> value at given level <= decision level */
void trail_add_propagation(mcsat_trail_t* trail, variable_t x, const mcsat_value_t* value, uint32_t id, uint32_t level);

/** Returns the type of assignment the variable has */
static inline
assignment_type_t trail_get_assignment_type(const mcsat_trail_t* trail, variable_t x) {
  assert(x < trail->type.size);
  return trail->type.data[x];
}

/** Return the id of the source that propagated/decided the value of the given variable */
static inline
uint32_t trail_get_source_id(const mcsat_trail_t* trail, variable_t x) {
  assert(x < trail->id.size);
  return trail->id.data[x];
};

/** Pop the top of the trail (propagation) */
void trail_pop_propagation(mcsat_trail_t* trail);

/** Pop the top of the trail (decision) */
void trail_pop_decision(mcsat_trail_t* trail);

/** Pop all until (and including) the last decision */
void trail_pop(mcsat_trail_t* trail);

/** Get the log of unassigned variables (which you can/should clear) */
static inline
ivector_t* trail_get_unassigned(mcsat_trail_t* trail) {
  return &trail->unassigned;
}

/** Mark all the variables in the trail */
void trail_gc_mark(mcsat_trail_t* trail, gc_info_t* gc_vars);

/** Sweep any data associated with the unmarked variables  */
void trail_gc_sweep(mcsat_trail_t* trail, const gc_info_t* gc_vars);

/** compare variables based on the trail level, unassigned to the front, then assigned ones by decreasing level */
bool trail_variable_compare(const mcsat_trail_t *trail, variable_t t1, variable_t t2);

/** Clear model cache */
void trail_model_cache_clear(mcsat_trail_t* trail);

#endif /* MCSAT_TRAIL_H_ */
