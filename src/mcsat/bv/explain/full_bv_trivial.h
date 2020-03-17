/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#pragma once

#include "mcsat/bv/bv_explainer.h"

/** Allocate the subexplainer and setup the methods */
bv_subexplainer_t* full_bv_trivial_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval);
