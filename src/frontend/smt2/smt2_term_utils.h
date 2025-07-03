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

#ifndef __SMT2_TERM_UTILS_H
#define __SMT2_TERM_UTILS_H

#include "context/context.h"
#include "utils/int_vectors.h"
#include "utils/int_hash_sets.h"

/*
 * Collect all boolean atoms from a given term t.
 * - ctx: the context, used to get the term table
 * - t: the term to explore
 * - h: the hash set where the atoms are stored.
 *      the set must be initialized.
 */
extern void collect_atoms(context_t *ctx, term_t t, int_hset_t *h);

/*
 * Given a term t and a vector of assumptions, collect all assumptions
 * that appear as sub-terms of t.
 * - ctx: the context
 * - t: the term to explore
 * - assumptions: vector of assumption terms
 * - result: output vector. The relevant assumptions are added to this vector.
 */
extern void filter_assumptions_by_term(context_t *ctx, term_t t, const ivector_t *assumptions, ivector_t *result);


#endif /* __SMT2_TERM_UTILS_H */ 