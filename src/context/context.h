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
 * CONTEXT OPERATIONS
 */

#ifndef __CONTEXT_H
#define __CONTEXT_H

#include "api/search_parameters.h"
#include "context/context_utils.h"


/****************************
 *  ARCHITECTURE & SOLVERS  *
 ***************************/

/*
 * Check whether a given architecture includes a specific solver
 */
extern bool context_arch_has_egraph(context_arch_t arch);
extern bool context_arch_has_bv(context_arch_t arch);
extern bool context_arch_has_fun(context_arch_t arch);
extern bool context_arch_has_arith(context_arch_t arch);
extern bool context_arch_has_simplex(context_arch_t arch);
extern bool context_arch_has_ifw(context_arch_t arch);
extern bool context_arch_has_rfw(context_arch_t arch);
extern bool context_arch_has_mcsat(context_arch_t arch);


/********************************
 *  INITIALIZATION AND CONTROL  *
 *******************************/

/*
 * Initialize ctx for the given logic, mode, and architecture
 * - terms = term table for this context
 * - qflag = false means quantifier-free variant
 * - qflag = true means quantifiers allowed
 * If arch is one of the ARCH_AUTO_... variants, then mode must be ONECHECK
 */
extern void init_context(context_t *ctx, term_table_t *terms, smt_logic_t logic,
                         context_mode_t mode, context_arch_t arch, bool qflag);


/*
 * Deletion
 */
extern void delete_context(context_t *ctx);


/*
 * Reset: remove all assertions
 */
extern void reset_context(context_t *ctx);


/*
 * Set the trace:
 * - the current tracer must be NULL.
 * - the tracer is also attached to the context's smt_core
 *   (so all solvers can use it to print stuff).
 */
extern void context_set_trace(context_t *ctx, tracer_t *trace);


/*
 * Push and pop
 * - should not be used if the push_pop option is disabled
 */
extern void context_push(context_t *ctx);
extern void context_pop(context_t *ctx);



/*************
 *  OPTIONS  *
 ************/


/*
 * Functions for testing/setting optional features are defined
 * in context_utils.h and are available in any module that
 * imports context.h. We define a few more here that are
 * related to the arithmetic solver.
 */

/*
 * Options for the simplex solver. If the context already contains
 * a simplex solver, then these options are set in this solver.
 * Otherwise, they will be set at the time the simplex solver is
 * constructed and added to the simplex solver.
 */
extern void enable_splx_eager_lemmas(context_t *ctx);
extern void disable_splx_eager_lemmas(context_t *ctx);
extern void enable_splx_periodic_icheck(context_t *ctx);
extern void disable_splx_periodic_icheck(context_t *ctx);
extern void enable_splx_eqprop(context_t *ctx);
extern void disable_splx_eqprop(context_t *ctx);


/*
 * Check which variant of the arithmetic solver is present
 */
extern bool context_has_idl_solver(context_t *ctx);
extern bool context_has_rdl_solver(context_t *ctx);
extern bool context_has_simplex_solver(context_t *ctx);



/****************************
 *   ASSERTIONS AND CHECK   *
 ***************************/

/*
 * Assert a boolean formula f.
 *
 * The context status must be IDLE.
 *
 * Return code:
 * - TRIVIALLY_UNSAT means that an inconsistency is detected
 *   (in that case the context status is set to UNSAT)
 * - CTX_NO_ERROR means no internalization error and status not
 *   determined
 * - otherwise, the code is negative. The assertion could
 *   not be processed.
 */
extern int32_t assert_formula(context_t *ctx, term_t f);


/*
 * Assert all formulas f[0] ... f[n-1]
 * same return code as above.
 */
extern int32_t assert_formulas(context_t *ctx, uint32_t n, const term_t *f);


/*
 * Assert all formulas f[0] ... f[n-1] during quantifier instantiation
 * The context status must be SEARCHING.
 *
 * Return code:
 * - TRIVIALLY_UNSAT means that an inconsistency is detected
 *   (in that case the context status is set to UNSAT)
 * - CTX_NO_ERROR means no internalization error and status not
 *   determined
 * - otherwise, the code is negative to report an error.
 */
extern int32_t quant_assert_formulas(context_t *ctx, uint32_t n, const term_t *f);


/*
 * Convert boolean term t to a literal l in context ctx
 * - return a negative code if there's an error
 * - return a literal (l >= 0) otherwise.
 */
extern int32_t context_internalize(context_t *ctx, term_t t);


/*
 * Build an assumption for Boolean term t:
 * - this converts t to a literal l in context ctx
 *   then create an indicator variable x in the core
 *   and add the clause (x => l) in the core.
 * - return a negative code if t can't be internalized
 * - return the literal x otherwise (where x>=0).
 */
extern int32_t context_add_assumption(context_t *ctx, term_t t);


/*
 * Add the blocking clause to ctx
 * - ctx->status must be either SAT or UNKNOWN
 * - this collects all decision literals in the current truth assignment
 *   (say l_1, ..., l_k) then clears the current assignment and adds the
 *  clause ((not l_1) \/ ... \/ (not l_k)).
 *
 * Return code:
 * - TRIVIALLY_UNSAT: means that the blocking clause is empty (i.e., k = 0)
 *   (in that case, the context status is set to UNSAT)
 * - CTX_NO_ERROR: means that the blocking clause is not empty (i.e., k > 0)
 *   (In this case, the context status is set to IDLE)
 */
extern int32_t assert_blocking_clause(context_t *ctx);


/*
 * Check whether the context is consistent
 * - parameters = search and heuristic parameters to use
 * - if parameters is NULL, the default values are used
 *
 * return status: either STATUS_UNSAT, STATUS_SAT, STATUS_UNKNOWN,
 * STATUS_INTERRUPTED (these codes are defined in smt_core.h)
 */
extern smt_status_t check_context(context_t *ctx, const param_t *parameters);


/*
 * Check under assumptions
 * - parameters = search and heuristic parameters to use
 * - if parameter is NULL, default values are used
 * - a = array of n literals = n assumptions
 * - each a[i] must be defined in ctx->core
 *
 * return status: either STATUS_UNSAT, STATUS_SAT, STATUS_UNKNOWN,
 * STATUS_INTERRUPTED
 *
 * If status is STATUS_UNSAT then the assumptions are inconsistent
 */
extern smt_status_t check_context_with_assumptions(context_t *ctx, const param_t *parameters, uint32_t n, const literal_t *a);

/*
 * Check satisfiability under model: check whether the assertions stored in ctx
 * conjoined with the assignment that the model gives to t is satisfiable.
 *
 * - params is an optional structure to store heuristic parameters
 * - if params is NULL, default parameter settings are used.
 * - model = model to assume
 * - t = variables to use from the model (size = n)
 *
 * return status: either STATUS_UNSAT, STATUS_SAT, STATUS_UNKNOWN,
 * STATUS_INTERRUPTED
 *
 * If status is STATUS_UNSAT then the context and model are inconsistent
 */
extern smt_status_t check_context_with_model(context_t *ctx, const param_t *params, model_t* mdl, uint32_t n, const term_t t[]);


/*
 * Build a model: the context's status must be STATUS_SAT or STATUS_UNKNOWN
 * - model must be initialized (and empty)
 * - the model maps a value to every uninterpreted terms present in ctx's
 *   internalization tables
 * - if model->has_alias is true, the term substitution defined by ctx->intern_tbl
 *   is copied into the model
 */
extern void context_build_model(model_t *model, context_t *ctx);

/*
 * Build a model for the current context (including all satellite solvers)
 * - the context status must be SAT (or UNKNOWN)
 * - if model->has_alias is true, we store the term substitution
 *   defined by ctx->intern_tbl into the model
 * - cleanup of satellite models needed using clean_solver_models()
 */
extern void build_model(model_t *model, context_t *ctx);

/*
 * Cleanup solver models
 */
extern void clean_solver_models(context_t *ctx);


/*
 * Build an unsat core: the context's status must be STATUS_UNSAT
 * - the unsat core is returned in vector *v
 * - if there are no assumption, the core is empty
 * - otherwise, the core is constructed from the bad_assumption
 *   and copied in v
 */
extern void context_build_unsat_core(context_t *ctx, ivector_t *v);


/*
 * Get the model interpolant: the context's status must be STATUS_USAT
 */
extern term_t context_get_unsat_model_interpolant(context_t *ctx);

/*
 * Interrupt the search
 * - this can be called after check_context from a signal handler
 * - this interrupts the current search
 * - if clean_interrupt is enabled, calling context_cleanup will
 *   restore the solver to a good state, equivalent to the state
 *   before the call to check_context
 * - otherwise, the solver is in a bad state from which new assertions
 *   can't be processed. Cleanup is possible via pop (if push/pop is supported)
 *   or reset.
 */
extern void context_stop_search(context_t *ctx);


/*
 * Cleanup after check is interrupted
 * - must not be called if the clean_interrupt option is disabled
 * - restore the context to a good state (status = IDLE)
 */
extern void context_cleanup(context_t *ctx);


/*
 * Clear boolean assignment and return to the IDLE state.
 * - this can be called after check returns UNKNOWN or SEARCHING
 *   provided the context's mode isn't ONECHECK
 * - after this call, additional formulas can be asserted and
 *   another call to check_context is allowed. Model construction
 *   is no longer possible until the next call to check_context.
 */
extern void context_clear(context_t *ctx);


/*
 * Cleanup after the search returned UNSAT
 * - if there are assumptions, they are removed
 * - if the clean_interrupt option is enabled, the state
 *   is restored to what it was at the start of search
 * - otherwise, this does nothing.
 *
 * On exit, the context's status can be either STATUS_IDLE
 * (if assumptions were removed) or STATUS_UNSAT otherwise.
 *
 * NOTE: Call this before context_pop(ctx) if the context status
 * is unsat.
 */
extern void context_clear_unsat(context_t *ctx);


/*
 * Precheck: force generation of clauses and other stuff that's
 * constructed lazily by the solvers. For example, this
 * can be used to convert all the constraints asserted in the
 * bitvector to clauses so that we can export the result to DIMACS.
 *
 * If ctx status is IDLE:
 * - the function calls 'start_search' and does one round of propagation.
 * - if this results in UNSAT, the function returns UNSAT
 * - otherwise the function returns UNKNOWN and restore the status to
 *   IDLE
 *
 * If ctx status is not IDLE, the function returns it and does nothing
 * else.
 */
extern smt_status_t precheck_context(context_t *ctx);


/*
 * Solve using another SAT solver
 * - sat_solver = name of the external SAT solver to use
 *   sat_solver can be either "y2sat" or "cadical"
 * - verbosity = verbosity level
 *
 * This may be used only for BV or pure SAT problems
 *
 * If ctx status is IDLE:
 * - perform one round of propagation to convert the problem to CNF
 * - call an external SAT solver on the CNF problem
 *
 * If ctx status is not IDLE, the function returns it and does nothing
 * else.
 */
extern smt_status_t check_with_delegate(context_t *ctx, const char *sat_solver, uint32_t verbosity);


/*
 * Bit-blast then export to DIMACS
 * - filename = name of the output file
 * - status = status of the context after bit-blasting
 *
 * If ctx status is IDLE
 * - perform one round of propagation to conver the problem to CNF
 * - export the CNF to DIMACS
 *
 * If ctx status is not IDLE,
 * - store the stauts in *status and do nothing else
 *
 * Return code:
 *  1 if the DIMACS file was created
 *  0 if the problem was solved by the propagation round
 * -1 if there was an error in creating or writing to the file.
 */
extern int32_t bitblast_then_export_to_dimacs(context_t *ctx, const char *filename, smt_status_t *status);

/*
 * Simplify then export to DIMACS
 * - filename = name of the output file
 * - status = status of the context after CNF conversion + preprocessing
 *
 * If ctx status is IDLE
 * - perform one round of propagation to convert the problem to CNF
 * - export the CNF to y2sat for extra preprocessing then export that to DIMACS
 *
 * If ctx status is not IDLE, the function stores it in *status
 * If y2sat preprocessing solves the formula, return the status also in *status
 *
 * Return code:
 *  1 if the DIMACS file was created
 *  0 if the problems was solved by preprocessing (or if ctx status is not IDLE)
 * -1 if there was an error creating or writing to the file.
 */
extern int32_t process_then_export_to_dimacs(context_t *ctx, const char *filename, smt_status_t *status);



/*
 * FOR TESTING/DEBUGGING
 */

/*
 * Preprocess formula f or array of formulas f[0 ... n-1]
 * - this does flattening + build substitutions
 * - return code: as in assert_formulas
 * - the result is stored in the internal vectors
 *     ctx->top_interns
 *     ctx->top_eqs
 *     ctx->top_atoms
 *     ctx->top_formulas
 *   + ctx->intern stores substitutions
 */
extern int32_t context_process_formula(context_t *ctx, term_t f);
extern int32_t context_process_formulas(context_t *ctx, uint32_t n, term_t *f);



/*
 * Read the status: returns one of
 *  STATUS_IDLE        (before check_context)
 *  STATUS_SEARCHING   (during check_context)
 *  STATUS_UNKNOWN
 *  STATUS_SAT
 *  STATUS_UNSAT
 *  STATUS_INTERRUPTED
 */
static inline smt_status_t context_status(context_t *ctx) {
  if (ctx->arch == CTX_ARCH_MCSAT) {
    return mcsat_status(ctx->mcsat);
  } else {
    return smt_status(ctx->core);
  }
}


/*
 * Read the base_level (= number of calls to push)
 */
static inline uint32_t context_base_level(context_t *ctx) {
  return ctx->base_level;
}


/*
 * Value of a Boolean term in ctx
 * - t must be a Boolean term
 *
 * The result can be
 * - VAL_TRUE  if t is true
 * - VAL_FALSE if t is false
 * - VAL_UNDEF_FALSE or VAL_UNDEF_TRUE otherwise (value is not known)
 */
extern bval_t context_bool_term_value(context_t *ctx, term_t t);


/*
 * GARBAGE-COLLECTION SUPPORT
 */

/*
 * Mark all terms present in ctx (to make sure they survive the
 * next call to term_table_gc).
 */
extern void context_gc_mark(context_t *ctx);



#endif /* __CONTEXT_H */
