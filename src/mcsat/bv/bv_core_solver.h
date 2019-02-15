/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#pragma once

#include "mcsat/mcsat_types.h"
#include "mcsat/variable_db.h"
#include "mcsat/utils/substitution.h"
#include "utils/int_vectors.h"
#include "context/context_types.h"

#include "utils/int_array_sort2.h"

/** Solver for solving cores with assumptions */
typedef struct {

  /** Whether to do incremental solving */
  bool incremental;

  /** The substitution */
  substitution_t subst;

  /** The terms to assign (old terms, not new) */
  ivector_t vars_to_assign;

  /** MCSAT plugin context */
  plugin_context_t* ctx;

  /** Yices config */
  ctx_config_t* config;

  /** Yices context */
  context_t* yices_ctx;

} bv_core_solver_t;

/** Construct the solver */
void bv_core_solver_construct(bv_core_solver_t* solver, plugin_context_t* ctx, bool incremental);

/** Destruct the solver */
void bv_core_solver_destruct(bv_core_solver_t* solver);

/** Reset the solver */
void bv_core_solver_reset(bv_core_solver_t* solver);

/** Add a new variable (for assumption/free variable) */
void bv_core_solver_add_variable(bv_core_solver_t* solver, variable_t var, bool with_value);

/** Assert something (term version) */
void bv_core_solver_assert_term(bv_core_solver_t* solver, variable_t assertion_term);

/** Assert something (variable version) */
void bv_core_solver_assert_var(bv_core_solver_t* solver, variable_t var);

/** Solve the problem and get the core */
void bv_core_solver_solve_and_get_core(bv_core_solver_t* solver, term_vector_t* core);
