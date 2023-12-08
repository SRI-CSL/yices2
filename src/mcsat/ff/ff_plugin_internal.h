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

#ifndef FF_PLUGIN_INTERNAL_H
#define FF_PLUGIN_INTERNAL_H

#include <poly/poly.h>

#include "ff_plugin_internal.h"

#include "mcsat/plugin.h"
#include "mcsat/unit_info.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/utils/int_mset.h"

#include "terms/term_manager.h"

typedef struct poly_constraint_db_struct poly_constraint_db_t;
typedef struct poly_constraint_struct poly_constraint_t;

typedef struct ff_plugin_s ff_plugin_t;

struct ff_plugin_s {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** The watch list manager */
  watch_list_manager_t wlm;

#if 0
  /** Last variable that was decided, but yet unprocessed */
  variable_t last_decided_and_unprocessed;

  /** Map from constraint variables to the constraint_unit_info_t enum */
  int_hmap_t constraint_unit_info;

  /** Map from constraint variables to the variables they are unit in */
  int_hmap_t constraint_unit_var;

  /** Next index of the trail to process */
  uint32_t trail_i;
#endif

  /** The conflict variable (one with empty feasible set) */
  variable_t conflict_variable;

#if 0
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
#endif

  struct {
    statistic_int_t* propagations;
    statistic_int_t* conflicts;
    statistic_int_t* conflicts_assumption;
    statistic_int_t* constraints_attached;
    statistic_int_t* evaluations;
    statistic_int_t* constraint;
  } stats;

#if 0
  /** Database of polynomial constraints */
  poly_constraint_db_t* constraint_db;

  /** Map from variables to their feasible sets */
  feasible_set_db_t* feasible_set_db;

  /** Data related to libpoly */
  struct {

    /** Libpoly variable database */
    lp_variable_db_t* lp_var_db;
    /** Libpoly Variable order */
    lp_variable_order_t* lp_var_order;
    /** Size of the variable order (for backtracking) */
    uint32_t lp_var_order_size;
    /** Libpoly polynomioal context */
    lp_polynomial_context_t* lp_ctx;
    /** Libpoly model */
    lp_assignment_t* lp_assignment;
    /** Interval assignment for bound inference */
    lp_interval_assignment_t* lp_interval_assignment;

    /** Map from libpoly variables to mcsat variables */
    int_hmap_t lp_to_mcsat_var_map;
    /** Map from mcsat variables to libpoly variables */
    int_hmap_t mcsat_to_lp_var_map;
  } lp_data;

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
