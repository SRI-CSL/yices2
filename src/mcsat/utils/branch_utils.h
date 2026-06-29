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

#endif /* MCSAT_BRANCH_UTILS_H_ */
