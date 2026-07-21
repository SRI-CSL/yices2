/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#pragma once

#include "mcsat/bv/bv_explainer.h"

/** Allocate the subexplainer and setup the methods */
bv_subexplainer_t* eq_ext_con_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval);
