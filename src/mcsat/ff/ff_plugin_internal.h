/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef FF_PLUGIN_INTERNAL_H
#define FF_PLUGIN_INTERNAL_H

#include <poly/poly.h>

#include "mcsat/ff/ff_plugin_internal.h"
#include "mcsat/ff/ff_feasible_set_db.h"

#include "mcsat/plugin.h"
#include "mcsat/unit_info.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/utils/lp_data.h"
#include "mcsat/utils/lp_utils.h"
#include "mcsat/utils/lp_constraint_db.h"
#include "mcsat/utils/int_mset.h"

#include "terms/term_manager.h"

typedef struct ff_plugin_s ff_plugin_t;

struct ff_plugin_s {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** The watch list manager */
  watch_list_manager_t wlm;

  /** The unit info */
  constraint_unit_info_t unit_info;

  /** Data related to libpoly */
  lp_data_t *lp_data;

  /** Last variable that was decided, but yet unprocessed */
  variable_t last_decided_and_unprocessed;

  /** Next index of the trail to process */
  uint32_t trail_i;

  /** The conflict variable (one with empty feasible set) */
  variable_t conflict_variable;

#if 0
  /** The conflict variable (assumption not in feasible set) */
  variable_t conflict_variable_assumption;

  /** The value that got the assumptions variable in trouble */
  lp_value_t conflict_variable_value;

  /** Bound variable term */
  term_t global_bound_term;

#endif

  /** Variables processed in propagation */
  ivector_t processed_variables;

  /** Size of processed (for backtracking) */
  uint32_t processed_variables_size;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  struct {
    statistic_int_t* propagations;
    statistic_int_t* conflicts;
    statistic_int_t* conflicts_assumption;
    statistic_int_t* constraints_attached;
    statistic_int_t* evaluations;
    statistic_int_t* constraint;
    statistic_int_t* variable_hints;
  } stats;

  /** Database of polynomial constraints */
  poly_constraint_db_t* constraint_db;

  /** Map from variables to their feasible sets */
  ff_feasible_set_db_t* feasible_set_db;

#if 0
  /** Buffer for evaluation */
  int_hmap_t evaluation_value_cache;
  int_hmap_t evaluation_timestamp_cache;

  /** Buffer for feasible set computation (for true/false */
  int_hmap_t feasible_set_cache_top_var[2];   // Top var when cached
  int_hmap_t feasible_set_cache_timestamp[2]; // Top timestamp of other variables when cached
  ptr_hmap_t feasible_set_cache[2];           // The cache
#endif

  /** Arithmetic buffer for computation */
  rba_buffer_t buffer;

  /** Exception handler */
  jmp_buf* exception;

};

void ff_plugin_get_constraint_variables(ff_plugin_t* ff, term_t constraint, int_mset_t* vars_out);

void ff_plugin_get_term_variables(ff_plugin_t* ff, term_t t, int_mset_t* vars_out);


#endif /* FF_PLUGIN_INTERNAL_H */
