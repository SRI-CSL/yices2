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

#ifndef __MCSAT_SATELLITE_H
#define __MCSAT_SATELLITE_H

#include <stdint.h>
#include <stdbool.h>

#include "context/context_types.h"
#include "solvers/egraph/egraph_types.h"

typedef struct mcsat_satellite_s mcsat_satellite_t;

extern mcsat_satellite_t *new_mcsat_satellite(context_t *ctx);
extern void delete_mcsat_satellite(mcsat_satellite_t *sat);

extern th_ctrl_interface_t *mcsat_satellite_ctrl_interface(mcsat_satellite_t *sat);
extern th_smt_interface_t *mcsat_satellite_smt_interface(mcsat_satellite_t *sat);
extern th_egraph_interface_t *mcsat_satellite_egraph_interface(mcsat_satellite_t *sat);

extern int32_t mcsat_satellite_assert_formulas(mcsat_satellite_t *sat, uint32_t n, const term_t *a);

/*
 * Register a Boolean atom term tracked by the supplementary MCSAT satellite.
 * - atom must be a Boolean term.
 * - l must be a positive core literal.
 * - *obj is set to a satellite-owned atom object for egraph tagging/dispatch.
 * Return code:
 * - CTX_NO_ERROR on success
 * - a negative internalization code on error.
 */
/*
 * Register one tracked atom/literal pair.
 * - if obj is non-NULL, create an opaque atom object for egraph tagging.
 * - if obj is NULL, register as observation-only (no egraph atom tag).
 */
extern int32_t mcsat_satellite_register_atom(mcsat_satellite_t *sat, term_t atom, literal_t l, void **obj);

/*
 * Record a mapping from an arithmetic theory variable to the source term.
 * This is used to materialize eq/diseq notifications into MCSAT assumptions.
 */
extern void mcsat_satellite_register_arith_term(mcsat_satellite_t *sat, thvar_t x, term_t t);

/*
 * Copy search parameters relevant to supplementary checking.
 */
extern void mcsat_satellite_set_search_parameters(mcsat_satellite_t *sat, const param_t *params);

/*
 * Return the most recent UNSAT model interpolant from the satellite solver.
 * Returns NULL_TERM if unavailable.
 */
extern term_t mcsat_satellite_get_unsat_model_interpolant(mcsat_satellite_t *sat);
extern void mcsat_satellite_set_unsat_model_interpolant(mcsat_satellite_t *sat, term_t t);
extern term_t mcsat_satellite_compute_unsat_model_interpolant(mcsat_satellite_t *sat, const param_t *params, uint32_t n, const term_t *a);

/*
 * Overlay model values from the supplementary MCSAT context.
 */
extern void mcsat_satellite_build_model(mcsat_satellite_t *sat, model_t *model);

/*
 * Trace + GC support.
 */
extern void mcsat_satellite_set_trace(mcsat_satellite_t *sat, tracer_t *trace);
extern void mcsat_satellite_gc_mark(mcsat_satellite_t *sat);

#endif /* __MCSAT_SATELLITE_H */
