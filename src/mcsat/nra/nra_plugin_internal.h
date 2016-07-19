/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#pragma once

#include <poly/poly.h>

#include "mcsat/plugin.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/utils/int_mset.h"
#include "mcsat/nra/feasible_set_db.h"

#include "terms/term_manager.h"

typedef struct poly_constraint_db_struct poly_constraint_db_t;
typedef struct poly_constraint_struct poly_constraint_t;

// Variable check to track for debugging
// #define TRACK_VAR(x) (x == 731)
#define TRACK_VAR(x) false

// Constraint check to track for debugging
// #define TRACK_CONSTRAINT(x) (x == 2640)
#define TRACK_CONSTRAINT(x) false

typedef enum {
  /** The constraint is not unit, nor fully assigned */
  CONSTRAINT_UNKNOWN,
  /** The constraint is unit */
  CONSTRAINT_UNIT,
  /** All variables of the constraint are assigned */
  CONSTRAINT_FULLY_ASSIGNED
} constraint_unit_info_t;

typedef struct nra_plugin_s {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** The watch list manager */
  watch_list_manager_t wlm;

  /** Last variable that was decided, but yet unprocessed */
  variable_t last_decided_and_unprocessed;

  /** Map from constraint variables to the constraint_unit_info_t enum */
  int_hmap_t constraint_unit_info;

  /** Map from constraint variables to the variables they are unit in */
  int_hmap_t constraint_unit_var;

  /** Next index of the trail to process */
  uint32_t trail_i;

  /** The conflict variable (one with empty feasible set) */
  variable_t conflict_variable;

  /** The conflict variable (one with empty int feasible set) */
  variable_t conflict_variable_int;

  /** Variables processed in propagation */
  ivector_t processed_variables;

  /** Size of processed (for backtracking) */
  uint32_t processed_variables_size;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  struct {
    uint32_t* propagations;
    uint32_t* conflicts;
    uint32_t* conflicts_int;
    uint32_t* constraints_attached;
  } stats;

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

    /** Map from libpoly variables to mcsat variables */
    int_hmap_t lp_to_mcsat_var_map;
    /** Map from mcsat variables to libpoly variables */
    int_hmap_t mcsat_to_lp_var_map;
  } lp_data;

  /** Arithmetic buffer for computation */
  rba_buffer_t buffer;

  /** Local term manager */
  term_manager_t tm;

  /** Exception handler */
  jmp_buf* exception;

} nra_plugin_t;

/**
 * Gets all the arithmetic variables from a non-atom t and adds their corresponding
 * mcsat variable to vars_out.
 */
void nra_plugin_get_term_variables(nra_plugin_t* nra, term_t t, int_mset_t* vars_out);

/**
 * Returns all arithmetic variables from a constraint (term) c and adds their corresponding
 * mcsat variable to vars_out. Returns false otherwise.
 */
void nra_plugin_get_constraint_variables(nra_plugin_t* nra, term_t c, int_mset_t* vars_out);

/** Check if there term has an lp variable */
int nra_plugin_term_has_lp_variable(nra_plugin_t* nra, term_t t);

/** Check if the mcsat variable has an lp variable */
int nra_plugin_variable_has_lp_variable(nra_plugin_t* nra, variable_t mcsat_var);

/** Add a variable corresponding to the term t to libpoly */
void nra_plugin_add_lp_variable_from_term(nra_plugin_t* nra, term_t t);

/** Add a variable corresponding to the mcsat variable to libpoly */
void nra_plugin_add_lp_variable(nra_plugin_t* nra, variable_t mcsat_var);

/** Get the libpoly variable corresponding to term t (should have been added first) */
lp_variable_t nra_plugin_get_lp_variable(nra_plugin_t* nra, variable_t t);

/** Get the mcsat variable from the libpoly variable */
variable_t nra_plugin_get_variable_from_lp_variable(nra_plugin_t* nra, lp_variable_t lp_var);

/** Set the unit info for the given constraint */
void nra_plugin_set_unit_info(nra_plugin_t* nra, variable_t constraint, variable_t unit_var, constraint_unit_info_t value);

/** Get the unit info for the given constraint */
constraint_unit_info_t nra_plugin_get_unit_info(nra_plugin_t* nra, variable_t constraint);

/** Get the unit variable for the given constraint */
variable_t nra_plugin_get_unit_var(nra_plugin_t* nra, variable_t constraint);

/** Report a conflict (variable is the one with an empty feasible set) */
void nra_plugin_report_conflict(nra_plugin_t* nra, trail_token_t* prop, variable_t variable);

/** Report a conflict (variable is the one with an empty int feasible set) */
void nra_plugin_report_int_conflict(nra_plugin_t* nra, trail_token_t* prop, variable_t variable);
