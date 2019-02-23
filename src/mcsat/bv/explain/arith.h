/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#pragma once

#include "mcsat/bv/bv_explainer.h"

/** Allocate the subexplainer and setup the methods */
bv_subexplainer_t* arith_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval);



/* #include "mcsat/bv/bv_evaluator.h" */

/* #include "mcsat/tracing.h" */
/* #include "mcsat/mcsat_types.h" */

/* #include "utils/int_vectors.h" */

  
/* /\** */
/*  * Main function. */
/*  * Gets a conflict core. Puts explanation in conflict */
/*  *\/ */

/* void bv_arith_get_conflict(plugin_context_t* ctx, bv_evaluator_t* eval, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict); */

/* // Test if in fragment */
/* bool bv_arith_applies_to(plugin_context_t* ctx, const ivector_t* conflict_core, variable_t conflict_var); */
