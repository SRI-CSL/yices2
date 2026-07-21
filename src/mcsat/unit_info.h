/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#pragma once

#include "mcsat/variable_db.h"
#include "mcsat/gc.h"
#include "utils/int_hash_map.h"

typedef enum {
  /** The constraint is not unit, nor fully assigned */
  CONSTRAINT_UNKNOWN,
  /** The constraint is unit */
  CONSTRAINT_UNIT,
  /** All variables of the constraint are assigned */
  CONSTRAINT_FULLY_ASSIGNED
} constraint_unit_state_t;

typedef struct {
  /** Map from constraint variables to the constraint_unit_state_t enum */
  int_hmap_t constraint_unit_info;

  /** Map from constraint variables to the variables they are unit in */
  int_hmap_t constraint_unit_var;
} constraint_unit_info_t;

/** Init the constraint_unit_info_t */
void constraint_unit_info_init(constraint_unit_info_t *unit_info);

/** Destructs the constraint_unit_info_t */
void constraint_unit_info_destruct(constraint_unit_info_t *unit_info);

/** Sweeps the constraint maps to remove old variables */
void constraint_unit_info_gc_sweep(constraint_unit_info_t *unit_info, const gc_info_t* gc_vars);

/**
 * Setting status of constraint: if value is CONSTRAINT_UNIT, then unit_var is the variable in which constraint is unit;
 * otherwise unit_var is variable_null
 */
void constraint_unit_info_set(constraint_unit_info_t *unit_info, variable_t constraint, variable_t unit_var, constraint_unit_state_t value);

/**
 * Updates the unit info when variable x gets unassigned.
 */
void constraint_unit_info_demote(constraint_unit_info_t *unit_info, variable_t constraint, variable_t x);

/** Are we tracking this constraint */
static inline
bool constraint_unit_info_has(const constraint_unit_info_t* unit_info, variable_t constraint) {
  return int_hmap_find(&unit_info->constraint_unit_info, constraint) != NULL;
}

/**
 * Getting status of constraint: if return value is CONSTRAINT_UNIT,
 * then bv_plugin_get_unit_var returns the variable in which constraint is unit
 * (otherwise it returns variable_null)
 */
static inline
constraint_unit_state_t constraint_unit_info_get(const constraint_unit_info_t* unit_info, variable_t constraint) {
  int_hmap_pair_t* find = int_hmap_find(&unit_info->constraint_unit_info, constraint);
  return find == NULL ? CONSTRAINT_UNKNOWN : find->val;
}

/** Get the unit variable for the given constraint */
static inline
variable_t constraint_unit_info_get_unit_var(const constraint_unit_info_t* unit_info, variable_t constraint) {
  int_hmap_pair_t* find = int_hmap_find(&unit_info->constraint_unit_var, constraint);
  return find == NULL ? variable_null : find->val;
}
