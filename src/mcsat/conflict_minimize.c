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
    int_hmap_add(marks, v, MCSAT_MIN_MARK_REMOVABLE);
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

typedef struct {
  const mcsat_trail_t* trail;
  uint32_t bool_plugin_id;
  const mcsat_reason_provider_t* provider;
} min_driver_data_t;

static int min_driver_classify(void* data, variable_t v) {
  min_driver_data_t* d = (min_driver_data_t*) data;
  if (trail_has_value_at_base(d->trail, v)) {
    return MCSAT_MIN_KIND_BASE;
  }
  if (trail_get_assignment_type(d->trail, v) == DECISION) {
    return MCSAT_MIN_KIND_DECISION;
  }
  if (trail_get_source_id(d->trail, v) == d->bool_plugin_id) {
    return MCSAT_MIN_KIND_REASON;
  }
  return MCSAT_MIN_KIND_NO_REASON;
}

static void min_driver_reason_vars(void* data, variable_t v, ivector_t* out) {
  min_driver_data_t* d = (min_driver_data_t*) data;
  d->provider->get_reason_vars(d->provider, v, out);
}

/* Insertion sort candidates ascending by trail index (clauses are small). */
static void min_sort_by_trail_index(const mcsat_trail_t* trail, ivector_t* cands) {
  uint32_t i, j;
  for (i = 1; i < cands->size; ++ i) {
    variable_t v = cands->data[i];
    uint32_t vi = trail_get_index(trail, v);
    j = i;
    while (j > 0 && trail_get_index(trail, cands->data[j - 1]) > vi) {
      cands->data[j] = cands->data[j - 1];
      j--;
    }
    cands->data[j] = v;
  }
}

void mcsat_minimize_conflict(conflict_t* conflict, const mcsat_trail_t* trail,
                             uint32_t bool_plugin_id, const mcsat_reason_provider_t* provider,
                             uint32_t max_depth, statistic_int_t* minimized_count) {
  uint32_t i;
  int_hmap_t marks;
  ivector_t candidates;
  ivector_t to_remove;

  init_int_hmap(&marks, 0);
  init_ivector(&candidates, 0);
  init_ivector(&to_remove, 0);

  /* 1. Seed KEEP for the UIP (asserting) variable(s): never removable. */
  ivector_t* uip_vars = conflict_get_variables(conflict);
  for (i = 0; i < uip_vars->size; ++ i) {
    variable_t v = uip_vars->data[i];
    if (v != variable_null && int_hmap_find(&marks, v) == NULL) {
      int_hmap_add(&marks, v, MCSAT_MIN_MARK_KEEP);
    }
  }

  /* 2. Walk all conflict top vars. Boolean-propagated, non-base, non-UIP vars
   *    are candidates; everything else is a KEEP anchor (theory/decision/base
   *    disjuncts that the recursion may legitimately terminate against). */
  /* Iterate the raw slots and skip empty (-1) and deleted (-2) entries.
   * The map accumulates deleted slots during resolution (int_hmap_erase), and
   * the int_hmap iterator API does NOT skip deleted entries, so we cannot use
   * it here -- mirror the deletion-safe scan used by conflict_print. */
  int_hmap_t* m2e = &conflict->var_to_element_map;
  for (i = 0; i < m2e->size; ++ i) {
    int_hmap_pair_t* p = m2e->data + i;
    if (p->key < 0) {
      continue;
    }
    variable_t v = p->key;
    if (int_hmap_find(&marks, v) != NULL) {
      continue; /* already a UIP keep */
    }
    if (!trail_has_value_at_base(trail, v)
        && trail_get_assignment_type(trail, v) == PROPAGATION
        && trail_get_source_id(trail, v) == bool_plugin_id) {
      ivector_push(&candidates, v);
    } else {
      int_hmap_add(&marks, v, MCSAT_MIN_MARK_KEEP);
    }
  }

  /* 3. Process candidates in trail order so reason vars that are themselves
   *    candidates are already resolved (kept/removable) when reached. */
  min_sort_by_trail_index(trail, &candidates);

  min_driver_data_t gdata;
  gdata.trail = trail;
  gdata.bool_plugin_id = bool_plugin_id;
  gdata.provider = provider;

  conflict_min_graph_t g;
  g.classify = min_driver_classify;
  g.reason_vars = min_driver_reason_vars;
  g.data = &gdata;

  for (i = 0; i < candidates.size; ++ i) {
    variable_t v = candidates.data[i];
    if (conflict_min_var_is_removable(&g, &marks, v, 0, max_depth)) {
      /* schedule the disjunct term(s) of v for removal */
      conflict_get_literals_of(conflict, v, &to_remove);
    } else {
      /* Not removable: the recursion already memoized v as POISON. Overwrite
       * it with KEEP so later candidates may legitimately anchor against v
       * (it stays in the clause). int_hmap_get returns the existing record. */
      int_hmap_get(&marks, v)->val = MCSAT_MIN_MARK_KEEP;
    }
  }

  /* 4. Apply removals. */
  for (i = 0; i < to_remove.size; ++ i) {
    conflict_remove_disjunct(conflict, to_remove.data[i]);
  }
  if (minimized_count != NULL) {
    *minimized_count += (statistic_int_t) to_remove.size;
  }

  delete_ivector(&to_remove);
  delete_ivector(&candidates);
  delete_int_hmap(&marks);
}
