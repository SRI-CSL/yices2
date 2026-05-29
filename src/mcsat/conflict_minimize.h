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

#ifndef MCSAT_CONFLICT_MINIMIZE_H_
#define MCSAT_CONFLICT_MINIMIZE_H_

#include "mcsat/conflict.h"
#include "mcsat/trail.h"
#include "mcsat/utils/statistics.h"

#include "utils/int_hash_map.h"
#include "utils/int_vectors.h"

/* Marks stored in the per-call memo map. */
#define MCSAT_MIN_MARK_REMOVABLE 1
#define MCSAT_MIN_MARK_POISON    2
#define MCSAT_MIN_MARK_KEEP      3

/* Static classification of a node (does not depend on marks). */
#define MCSAT_MIN_KIND_BASE      0  /* base-level: terminal success */
#define MCSAT_MIN_KIND_DECISION  1  /* decision: terminal failure   */
#define MCSAT_MIN_KIND_NO_REASON 2  /* theory propagation: failure  */
#define MCSAT_MIN_KIND_REASON    3  /* boolean clausal reason: recurse */

/*
 * Abstract reason graph the core recursion runs over. Implemented by the
 * MCSat driver (real trail/conflict) and by tests (synthetic graph).
 */
typedef struct conflict_min_graph_s {
  /* Classify v into one of MCSAT_MIN_KIND_*. */
  int (*classify)(void* data, variable_t v);
  /* For MCSAT_MIN_KIND_REASON vars: append the OTHER reason-clause variables. */
  void (*reason_vars)(void* data, variable_t v, ivector_t* out);
  void* data;
} conflict_min_graph_t;

/*
 * Returns true if v is redundant (its truth is implied by kept/base-level
 * nodes via the reason graph). Uses marks (var -> MCSAT_MIN_MARK_*) for
 * memoization; KEEP marks must be pre-seeded by the caller for anchor nodes.
 */
bool conflict_min_var_is_removable(const conflict_min_graph_t* g, int_hmap_t* marks,
                                   variable_t v, uint32_t depth, uint32_t max_depth);

/*
 * Side-effect-free provider of Boolean clausal reasons. get_reason_vars must
 * append the variables of v's reason clause other than v itself, WITHOUT any
 * activity/clause-score bumping. Only called for vars the driver has already
 * classified as MCSAT_MIN_KIND_REASON.
 */
typedef struct mcsat_reason_provider_s mcsat_reason_provider_t;
struct mcsat_reason_provider_s {
  void (*get_reason_vars)(const mcsat_reason_provider_t* self, variable_t var, ivector_t* out_vars);
};

/*
 * Minimize the conflict in place: drop Boolean-propagated disjuncts whose
 * truth is implied by the rest. Never removes the asserting (UIP) disjunct or
 * any theory/decision disjunct. Must be called while the conflict is fully
 * built and all its variables are still assigned on the trail (i.e. before the
 * final backtrack). Increments *minimized_count by the number of disjuncts
 * removed (if non-NULL).
 */
void mcsat_minimize_conflict(conflict_t* conflict, const mcsat_trail_t* trail,
                             uint32_t bool_plugin_id, const mcsat_reason_provider_t* provider,
                             uint32_t max_depth, statistic_int_t* minimized_count);

#endif /* MCSAT_CONFLICT_MINIMIZE_H_ */
