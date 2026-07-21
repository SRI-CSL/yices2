/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */
 
#pragma once

#include <poly/poly.h>

#include "mcsat/plugin.h"
#include "mcsat/unit_info.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/utils/int_mset.h"
#include "mcsat/utils/lp_data.h"
#include "mcsat/utils/lp_constraint_db.h"
#include "mcsat/na/feasible_set_db.h"

#include "terms/term_manager.h"

struct na_plugin_s {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** The watch list manager */
  watch_list_manager_t wlm;

  /** The unit info */
  constraint_unit_info_t unit_info;

  /** Last variable that was decided, but yet unprocessed */
  variable_t last_decided_and_unprocessed;

  /** Next index of the trail to process */
  uint32_t trail_i;

  /** The conflict variable (one with empty feasible set) */
  variable_t conflict_variable;

  /** The conflict variable (one with empty int feasible set) */
  variable_t conflict_variable_int;

  /** The conflict variable (assumption not in feasible set) */
  variable_t conflict_variable_assumption;

  /** The value that got the assumptions variable in trouble */
  lp_value_t conflict_variable_value;

  /** Bound variable term */
  term_t global_bound_term;

  /** Variables processed in propagation */
  ivector_t processed_variables;

  /** Size of processed (for backtracking) */
  uint32_t processed_variables_size;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  struct {
    statistic_int_t* propagations;
    statistic_int_t* conflicts;
    statistic_int_t* conflicts_int;
    statistic_int_t* conflicts_assumption;
    statistic_int_t* constraints_attached;
    statistic_int_t* evaluations;
    statistic_int_t* constraint_regular;
    statistic_int_t* constraint_root;
    statistic_avg_t* value_cache_usage;
    statistic_avg_t* value_cache_feasibility;
  } stats;

  /** Database of polynomial constraints */
  poly_constraint_db_t* constraint_db;

  /** Map from variables to their feasible sets */
  feasible_set_db_t* feasible_set_db;

  /** Data related to libpoly */
  lp_data_t lp_data;

  /** Buffer for evaluation */
  int_hmap_t evaluation_value_cache;
  int_hmap_t evaluation_timestamp_cache;

  /** Buffer for feasible set computation (for true/false) */
  int_hmap_t feasible_set_cache_top_var[2];   // Top var when cached
  int_hmap_t feasible_set_cache_timestamp[2]; // Top timestamp of other variables when cached
  ptr_hmap_t feasible_set_cache[2];           // The cache


  /** Arithmetic buffer for computation */
  rba_buffer_t buffer;

  /** Exception handler */
  jmp_buf* exception;

};

/**
 * Gets all the arithmetic variables from a non-atom t and adds their corresponding
 * mcsat variable to vars_out.
 */
void na_plugin_get_term_variables(na_plugin_t* na, term_t t, int_mset_t* vars_out);

/**
 * Returns all arithmetic variables from a constraint (term) c and adds their corresponding
 * mcsat variable to vars_out. Returns false otherwise.
 */
void na_plugin_get_constraint_variables(na_plugin_t* na, term_t c, int_mset_t* vars_out);

/** Notes a conflict without reporting it yet */
void na_plugin_note_conflict(na_plugin_t* na, variable_t variable);

/** Notes an int conflict without reporting it yet */
void na_plugin_note_int_conflict(na_plugin_t* na, variable_t variable);

/** Returns true if a conflict is noted but not reported */
int na_plugin_is_conflict_pending(na_plugin_t* na);

/** Report any noted real or int conflict */
void na_plugin_report_pending_conflict(na_plugin_t* na, trail_token_t* prop);

/** Report a conflict (variable is the one with an empty feasible set) */
void na_plugin_report_conflict(na_plugin_t* na, trail_token_t* prop, variable_t variable);

/** Report a conflict (variable is the one with an empty int feasible set) */
void na_plugin_report_int_conflict(na_plugin_t* na, trail_token_t* prop, variable_t variable);

/** Report a conflict (variable is the with value not in feasible set) */
void na_plugin_report_assumption_conflict(na_plugin_t* na, trail_token_t* prop, variable_t variable, const mcsat_value_t* value);
