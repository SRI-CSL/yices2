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

#include "unit_info.h"
#include <assert.h>

void constraint_unit_info_init(constraint_unit_info_t *unit_info) {
  init_int_hmap(&unit_info->constraint_unit_info, 0);
  init_int_hmap(&unit_info->constraint_unit_var, 0);
}

void constraint_unit_info_destruct(constraint_unit_info_t *unit_info) {
  delete_int_hmap(&unit_info->constraint_unit_info);
  delete_int_hmap(&unit_info->constraint_unit_var);
}

void constraint_unit_info_gc_sweep(constraint_unit_info_t *unit_info, const gc_info_t* gc_vars) {
  gc_info_sweep_int_hmap_keys(gc_vars, &unit_info->constraint_unit_info);
  gc_info_sweep_int_hmap_keys(gc_vars, &unit_info->constraint_unit_var);
}

void constraint_unit_info_set(constraint_unit_info_t *unit_info, variable_t constraint, variable_t unit_var, constraint_unit_state_t value) {
  int_hmap_pair_t* find = NULL;
  int_hmap_pair_t* unit_find = NULL;

  // Add unit tag
  find = int_hmap_find(&unit_info->constraint_unit_info, constraint);
  if (find == NULL) {
    // First time, just set
    int_hmap_add(&unit_info->constraint_unit_info, constraint, value);
  } else {
    assert(find->val != value);
    find->val = value;
  }

  // Add unit variable
  unit_find = int_hmap_find(&unit_info->constraint_unit_var, constraint);
  if (value == CONSTRAINT_UNIT) {
    if (unit_find == NULL) {
      int_hmap_add(&unit_info->constraint_unit_var, constraint, unit_var);
    } else {
      unit_find->val = unit_var;
    }
  } else {
    assert(unit_var == variable_null);
    if (unit_find != NULL) {
      unit_find->val = variable_null;
    }
  }
}
