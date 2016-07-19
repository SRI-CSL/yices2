/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
