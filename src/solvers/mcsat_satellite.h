/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef __MCSAT_SATELLITE_H
#define __MCSAT_SATELLITE_H

#include <stdint.h>
#include <stdbool.h>

#include "context/context_types.h"
#include "solvers/egraph/egraph_types.h"

typedef struct mcsat_satellite_s mcsat_satellite_t;

/*
 * Thread-safety note: the satellite shares the global term table with the
 * outer context.  In THREAD_SAFE builds, calls into the embedded MCSAT engine
 * and satellite-side term construction that can be reached from unlocked
 * CDCL(T) search are serialized by the global Yices mutex.
 */

extern mcsat_satellite_t *new_mcsat_satellite(context_t *ctx);
extern void delete_mcsat_satellite(mcsat_satellite_t *sat);

extern th_ctrl_interface_t *mcsat_satellite_ctrl_interface(mcsat_satellite_t *sat);
extern th_smt_interface_t *mcsat_satellite_smt_interface(mcsat_satellite_t *sat);
extern arith_observer_interface_t *mcsat_satellite_arith_observer_interface(mcsat_satellite_t *sat);

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
 * Build/export model values from the supplementary MCSAT context.
 * prepare_model solves the internal MCSAT context under the current completed
 * cube and exports exact MCSAT values into model. export_model is currently a
 * no-op hook kept to make the model-build phases explicit.
 */
extern bool mcsat_satellite_prepare_model(mcsat_satellite_t *sat, model_t *model);
extern void mcsat_satellite_export_model(mcsat_satellite_t *sat, model_t *model);
extern void mcsat_satellite_build_model(mcsat_satellite_t *sat, model_t *model);

/*
 * Return a value from the MCSAT-prepared model without querying simplex.
 */
extern bool mcsat_satellite_term_value(mcsat_satellite_t *sat, model_t *model, term_t t, value_t *v);
extern bool mcsat_satellite_arith_value_in_model(void *aux, thvar_t x, model_t *model, value_t *v);

/*
 * Trace + GC support.
 */
extern void mcsat_satellite_set_trace(mcsat_satellite_t *sat, tracer_t *trace);
extern void mcsat_satellite_gc_mark(mcsat_satellite_t *sat);

#endif /* __MCSAT_SATELLITE_H */
