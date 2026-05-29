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

#include "mcsat/conflict_minimize.h"

bool conflict_min_var_is_removable(const conflict_min_graph_t* g, int_hmap_t* marks,
                                   variable_t v, uint32_t depth, uint32_t max_depth) {
  int_hmap_pair_t* m = int_hmap_find(marks, v);
  if (m != NULL) {
    if (m->val == MCSAT_MIN_MARK_REMOVABLE || m->val == MCSAT_MIN_MARK_KEEP) {
      return true;
    }
    /* MCSAT_MIN_MARK_POISON */
    return false;
  }

  int kind = g->classify(g->data, v);
  if (kind == MCSAT_MIN_KIND_BASE) {
    return true;
  }
  if (kind == MCSAT_MIN_KIND_DECISION || kind == MCSAT_MIN_KIND_NO_REASON) {
    int_hmap_add(marks, v, MCSAT_MIN_MARK_POISON);
    return false;
  }
  if (depth >= max_depth) {
    int_hmap_add(marks, v, MCSAT_MIN_MARK_POISON);
    return false;
  }

  /* kind == MCSAT_MIN_KIND_REASON: recurse over the reason clause variables. */
  ivector_t reason_vars;
  init_ivector(&reason_vars, 0);
  g->reason_vars(g->data, v, &reason_vars);
  bool res = true;
  for (uint32_t i = 0; res && i < reason_vars.size; ++i) {
    res = conflict_min_var_is_removable(g, marks, reason_vars.data[i], depth + 1, max_depth);
  }
  delete_ivector(&reason_vars);

  int_hmap_add(marks, v, res ? MCSAT_MIN_MARK_REMOVABLE : MCSAT_MIN_MARK_POISON);
  return res;
}
