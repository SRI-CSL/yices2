/*
 * EF-Solver
 */

/*
 * Input are problems of the form
 *
 *   A(x) AND (FORALL y: B(y) => C(x y))
 *
 * where A, B, and C are quantifier-free formulas. The goal is to find
 * an assignment for the 'x' variables that makes the whole formula
 * true.
 *
 * We build a sequence of formulas A_0, A_1, .... that characterize
 * the set of potential solutions. We have
 *     A_0(x) => A(x)
 *     A_{k+1}(x) => A_k(x)
 *     A(x) AND not A_k(x) => EXISTS y: B(y) AND \not C(x y)
 *
 * Given A_k, we use the following procedure:
 *
 * 1) search for x_k that satisfies A_k
 *    if there are none then the EF problem is unsatisfiable
 *    and we're done.
 *
 * 2) check whether x_k is a solution:
 *    search for a y_k that statisfies B(y_k) AND \not C(x_k y_k)
 *    if there are none then x_k is a solution to the EFproblem,
 *    and we're done.
 *
 * 3) generalize: remove x_k from the solution space (and more
 *    elements if we can). This amounts to constructing a
 *    formula Z such that
 *       Z(x_k)  is true
 *       Z(x) AND A(x) => EXISTS y: B(y) AND \not C(x y)
 *
 * 4) iterate with A_{k+1} := (A_k AND not Z)
 *
 *
 * This general procedure requires:
 * - initialization: construct A_0
 * - generalization: contruct Z given and x_k, y_k
 *
 * For initialization:
 * - we can pick A_0 := A
 * - variant: search for solutions to
 *       (A(x) AND B(y) AND \not C(x, y))
 *
 * For generalization:
 * - no generalization: just define Z(x) as (x = x_k)
 * - substitution based: use Z(x) := C(x y_k)
 * - variants..
 *
 * The strongest generalization is quantifier elimination:
 * - construct a quantifier-free formula Z(x) such that
 *   Z(x) is equivalent to (EXISTS y: B(y) AND \not C(x y))
 */

#ifndef __EFSOLVER_H
#define __EFSOLVER_H

#include <stdint.h>
#include <stdbool.h>
#include <setjmp.h>

#include "yices_types.h"
#include "tracer.h"

#include "smt_logic_codes.h"
#include "search_parameters.h"
#include "context.h"

typedef struct ef_solver_s ef_solver_t;


/*
 * API (Provisional)
 */

/*
 * Initialize solver:
 * - table = term table for this solver
 * - logic = logic code (as defined in smt_logic_codes.h)
 *   SMT_UNKNOWN means no logic specified
 *   SMT_NONE means purely Boolean
 * - arch = solver architecture as defined in context.h
 */
extern void init_ef_solver(ef_solver_t *solver, term_table_t *terms,
			   smt_logic_t logic, context_arch_t arch);


/*
 * Delete:
 */
extern void delete_ef_solver(ef_solver_t *solver);


/*
 * Set the tracer
 * - solver's current tracer must be NULL
 */
extern void ef_solver_set_trace(ef_solver_t *solver, tracer_t *trace);


/*
 * Assert formulas f[0 ... n-1]
 * - all terms in f[0] ... f[n-1] must be Boolean
 * - return code: negative means that an error is detected
 * - 0 means no error
 * - 1 means trivially unsat
 */
extern int32_t ef_solver_assert_formulas(ef_solver_t *solver, uint32_t n, term_t *f);


/*
 * Variant: assert a single formula f
 */
extern int32_t ef_solver_assert_formula(ef_solver_t *solver, term_t f);


/*
 * Solve: check satisfiability
 */
extern smt_status_t ef_solver_check(ef_solver_t *solver);


/*
 * Build the model
 */
extern void ef_solver_build_model(ef_solver_t *solver);




#endif /* __EFSOLVER_H */
