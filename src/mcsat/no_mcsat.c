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
  return SMT_STATUS_ERROR;
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

void mcsat_solve(mcsat_solver_t *mcsat, const param_t *params, model_t* mdl, uint32_t n, const term_t t[]) {
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

