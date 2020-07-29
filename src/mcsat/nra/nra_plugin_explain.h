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
 
#pragma once

#include "nra_plugin_internal.h"
#include "utils/int_vectors.h"

/**
 * Explain the core in the conflict. Core is a set of constraint variables,
 * and conflict will a set if terms.
 *
 * pos: set of positive assumptions (to extend the trail)
 * neg: set of negative assumptions (to extend the trail)
 *
 * */
void nra_plugin_explain_conflict(nra_plugin_t* nra, const int_mset_t* pos, const int_mset_t* neg,
    const ivector_t* core, const ivector_t* lemma_reasons, ivector_t* conflict);

/**
 * Construct a cell for a given constraint that captures the current model. The cell is is
 * described in terms of polynomial constraints only.
 */
void nra_plugin_describe_cell(nra_plugin_t* nra, term_t p, ivector_t* out_literals);
