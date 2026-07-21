/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

 /*
 * This is placeholder to replace mcsat/solver.c when
 * Yices is compiled without mcsat support.
 *
 * This files provides all the functions listed in
 * mcsat/solver.h. They do nothing and should never be called.
 * We provide this so that the compilation works.
 */

#include "mcsat/solver.h"

mcsat_solver_t *mcsat_new(const context_t *ctx) {
  return NULL;
}

void mcsat_destruct(mcsat_solver_t *mcsat) {
}

smt_status_t mcsat_status(const mcsat_solver_t *mcsat) {
  return YICES_STATUS_ERROR;
}

void mcsat_reset(mcsat_solver_t *mcsat) {
}

void mcsat_clear(mcsat_solver_t* mcsat) {
}

void mcsat_push(mcsat_solver_t *mcsat) {
}

void mcsat_pop(mcsat_solver_t *mcsat) {
}

int32_t mcsat_assert_formulas(mcsat_solver_t *mcsat, uint32_t n, const term_t *f) {
  return 0;
}

void mcsat_set_model_hint(mcsat_solver_t* mcsat, model_t* mdl, uint32_t n_mdl_filter, const term_t mdl_filter[]) {
}

void mcsat_solve(mcsat_solver_t *mcsat, const param_t *params, model_t* mdl, uint32_t n, const term_t t[]) {
}

void mcsat_cleanup_assumptions(mcsat_solver_t* mcsat) {
}

void mcsat_set_tracer(mcsat_solver_t *mcsat, tracer_t *tracer) {
}

void mcsat_show_stats(mcsat_solver_t *mcsat, FILE *out) {
}

void mcsat_show_stats_fd(mcsat_solver_t *mcsat, int out) {
}

void mcsat_build_model(mcsat_solver_t* mcsat, model_t* model) {
}

void mcsat_gc_mark(mcsat_solver_t* mcsat) {
}

void mcsat_stop_search(mcsat_solver_t* mcsat) {
}

term_t mcsat_get_unsat_model_interpolant(mcsat_solver_t* mcsat) {
  return NULL_TERM;
}

void mcsat_set_unsat_result_from_labeled_interpolant(mcsat_solver_t* mcsat, term_t interpolant,
                                                     uint32_t n, const term_t* labels,
                                                     const term_t* assumptions) {
}
