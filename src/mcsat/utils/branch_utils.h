/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2026 SRI International.
 */

#ifndef MCSAT_BRANCH_UTILS_H_
#define MCSAT_BRANCH_UTILS_H_

#include "mcsat/plugin.h"

/*
 * Return whether Boolean term/literal t has the corresponding value in the
 * current MCSAT branch. Unassigned terms and non-Boolean values return false.
 */
extern bool mcsat_branch_bool_term_is_true(const plugin_context_t* ctx, term_t t);
extern bool mcsat_branch_bool_term_is_false(const plugin_context_t* ctx, term_t t);

/*
 * Equality-sensitivity callbacks. If the callbacks are not installed, keep the
 * old permissive behavior.
 */
extern bool mcsat_branch_type_is_equality_sensitive(plugin_context_t* ctx, type_t tau);
extern bool mcsat_branch_equality_sensitivity_is_frozen(plugin_context_t* ctx);

#endif /* MCSAT_BRANCH_UTILS_H_ */
