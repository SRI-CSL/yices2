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
 
#ifndef MCSAT_SOLVER_H_
#define MCSAT_SOLVER_H_

#include "include/yices_types.h"
#include "terms/terms.h"
#include "io/tracer.h"

#include "mcsat/mcsat_types.h"
#include "mcsat/options.h"

#include <setjmp.h>

/*
 * Allocate and construct the solver.
 */
mcsat_solver_t* mcsat_new(context_t* ctx);

/*
 * Destruct the solver.
 */
void mcsat_destruct(mcsat_solver_t* mcsat);

/*
 * Returns the status of the solver.
 */
smt_status_t mcsat_status(const mcsat_solver_t* mcsat);

/*
 * Remove all assertions.
 */
void mcsat_reset(mcsat_solver_t* mcsat);

/*
 * Clear: prepare for more assertions and checks.
 */
void mcsat_clear(mcsat_solver_t* mcsat);

/*
 * Push the user context.
 */
void mcsat_push(mcsat_solver_t* mcsat);

/*
 * Pop the user context.
 */
void mcsat_pop(mcsat_solver_t* mcsat);

/*
 * Assert all formulas f[0] ... f[n-1]. The context status must be IDLE.
 *
 * Return code:
 * - TRIVIALLY_UNSAT means that an inconsistency is detected
 *   (in that case the context status is set to UNSAT)
 * - CTX_NO_ERROR means no internalization error and status not
 *   determined
 * - otherwise, the code is negative to report an error.
 */
int32_t mcsat_assert_formulas(mcsat_solver_t *mcsat, uint32_t n, const term_t *f);

/*
 * Solve asserted constraints.
 *
 * @param params Heuristic parameters. If params is NULL, the default settings
 *               are used.
 */
void mcsat_solve(mcsat_solver_t* mcsat, const param_t *params);

/*
 * Add the model to the yices model
 */
void mcsat_build_model(mcsat_solver_t* mcsat, model_t* model);


/*
 * Set the tracer for the solver.
 */
void mcsat_set_tracer(mcsat_solver_t* mcsat, tracer_t* tracer);

/*
 * Show statistics.
 */
void mcsat_show_stats(mcsat_solver_t* mcsat, FILE* out);

/*
 * Set the excepetion handler. Should be done before, any call into the solver.
 */
void mcsat_set_exception_handler(mcsat_solver_t* mcsat, jmp_buf* handler);

#endif /* MCSAT_SOLVER_H_ */
