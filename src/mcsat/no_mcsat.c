/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

 /*
 * This is placeholder to replace mcsat/solver.c when
 * Yices is compiled witout mcsat support.
 *
 * This files provides all the functions listed in
 * mcsat/solver.h. They do nothing and should never be called.
 * We provide this so that the compilation works.
 */

#include "mcsat/solver.h"

mcsat_solver_t *mcsat_new(context_t *ctx) {
  return NULL;
}

void mcsat_destruct(mcsat_solver_t *mcsat) {
}

smt_status_t mcsat_status(const mcsat_solver_t *mcsat) {
  return STATUS_IDLE;
}

void mcsat_reset(mcsat_solver_t *mcsat) {
}

void mcsat_push(mcsat_solver_t *mcsat) {
}

void mcsat_pop(mcsat_solver_t *mcsat) {
}

int32_t mcsat_assert_formulas(mcsat_solver_t *mcsat, uint32_t n, const term_t *f) {
  return 0;
}

void mcsat_solve(mcsat_solver_t *mcsat, const param_t *params) {
}

void mcsat_set_tracer(mcsat_solver_t *mcsat, tracer_t *tracer) {
}

void mcsat_show_stats(mcsat_solver_t *mcsat, FILE *out) {
}

void mcsat_build_model(mcsat_solver_t* mcsat, model_t* model) {
}
