/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * EF-Solver
 */

/*
 * Input problems are stored in an ef_prob structure.
 * - prob->evars = existential variables (denoted by X)
 * - prob->uvars = universal variables   (denoted by Y)
 * - prob->conditions = a set of constraints on X:
 *    A1(X) and ... and At(X)
 * - and a finite list of universal constraints
 *
 * Each universal constraint has the form
 *
 *    (FORALL Y_i: B_i(Y_i) => C_i(X_i, Y_i))
 *
 * where Y_i is a subset of the universal variables
 *       X_i is a subset of the existential variables
 *       B_i is the assumption (on Y_i)
 *       C_i is the guarantee
 *
 *
 * The goal is to solve the exists/forall problem:
 *
 *  EXISTS X: A1(X) and ... and At(X)
 *   AND (FORALL Y_1: B_1(Y_1) => C_1(X_1, Y_1))
 *    ...
 *   AND (FORALL Y_k: B_k(Y_k) => C_k(X_k, Y_k))
 *
 *
 * General procedure
 * -----------------
 *
 * 1) initialize a context ctx with A1(X) ... At(X)
 *
 * 2) iterate the following loop
 *
 *    a) check whether ctx is satisfiable.
 *       If it's not, we're done. The EF-problem has no solution.
 *       If it is, let x be a model for ctx
 *
 *    b) check whether x is a solution:
 *
 *       For each universal constraint, check whether
 *
 *         B_i(Y_i) AND not C_i(X_i, Y_i) is satisfiable
 *         under the mapping X_i := x_i.
 *
 *       If it is, then let y_i be a model of this constraint.
 *
 *    c) If we find no witness in step b: exit. The model x is
 *       a solution to the EF-problem.
 *
 *       Otherwise, we have a witness y_i that shows why x is not
 *       good. That is, y_i is a counterexample to
 *
 *         (forall Y_i: B_i(Y_i) => C_i(X_i, Y_i)) with [X := x]
 *
 *       So y_i eliminates x from the candidate spaces.
 *       We want to generalize y_i: construct a formula Z(X_i) such
 *       that: 1) x satisfies Z(X_i)
 *             2) no other solution to Z(X_i) is a good candidate.
 *
 *       Once we have Z(X_i), we add \not Z(X_i) to the ctx and
 *       go back to a).
 *
 *
 * Different options for constructing Z
 * ------------------------------------
 * - Option 1: no generalization:    Z(X_i) is (X_i /= x_i)
 *    (just eliminate x_i)
 *
 * - Option 2: generalization by substitution:
 *     Z(X_i) is C(X_i, Y_i) with [Y_i := y_i]
 *    (eliminate any x_i for which y_i is a witness).
 *
 * - Option 3: quantifier elimination:
 *    rewrite (FORALL Y_i: B_i(Y_i) AND not C_i(X_i, Y_i))
 *      to     Z(X_i)
 *
 * - Other options: cheaper forms of quantifier elimination,
 *   driven by the witness y_i.
 *
 * Variant for initializing the exist context
 * ------------------------------------------
 * - Given constraint
 *
 *   (FORALL Y_i: B_i(Y_i) => C_i(X_i, Y_i))
 *
 *   we can sample y_s that satisfy B_i(Y_i). For every
 *   such y_i, we get a constraint C_i(X_i, y_i) by substitution.
 *   Then this constraint depends only on the existential
 *   variable, so we can add (C_i(X_i, y_i))) to the
 *   exists context (i.e., any good X_i must satisfy C_i(X_i, y_i)).
 *
 * Baseline implementation
 * -----------------------
 * - support Option 1 and 2.
 */

#ifndef __EFSOLVER_H
#define __EFSOLVER_H

#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>


#include "api/search_parameters.h"
#include "api/smt_logic_codes.h"
#include "context/context_types.h"
#include "exists_forall/ef_problem.h"
#include "io/tracer.h"

#include "yices_types.h"


/*
 * efsolver: stores a pointer to the ef_prob_t descriptor
 * + flags for context initialization: logic/arch
 * + search parameters (for now we use the same parameters for exists and forall)
 * + generalization option
 * + presampling setting: if max_samples is 0, no presampling
 *   otherwise, max_samples is used for sampling
 *
 * Internal data structures:
 * - exists_context, forall_context: pointers to contexts, allocated and initialized
 *   when needed
 * - evalue = array large enough to store the value of all exists variables
 * - uvalue = array large enough to store the value of all universal variables
 * - evalue_aux and uvalue_aux = auxiliary vectors (to store value vector of smaller
 *   sizes than evalue/uvalue)
 *
 * Flags for diagnostic
 * - status = status of the last call to check (either in the exists or
 *   the forall context)
 * - code = result of the last assertion (negative code is an error)
 */
typedef enum ef_gen_option {
  EF_NOGEN_OPTION,        // option 1 above
  EF_GEN_BY_SUBST_OPTION, // option 2 above
  EF_GEN_BY_PROJ_OPTION,  // model-based projection (cheap quantifier elimination)
  EF_GEN_AUTO_OPTION,     // select between PROJ or SUBST depending on variables
} ef_gen_option_t;


/*
 * Status + error report
 */
typedef enum ef_status {
  EF_STATUS_IDLE,              // before call to efsolver_check
  EF_STATUS_SEARCHING,         // while in efsolver_check
  EF_STATUS_UNKNOWN,           // max_iters reached
  EF_STATUS_SAT,               // satisfiable
  EF_STATUS_UNSAT,             // unsat
  EF_STATUS_INTERRUPTED,       // timeout
  EF_STATUS_SUBST_ERROR,       // error in a substitution
  EF_STATUS_TVAL_ERROR,        // error when converting model to constant terms
  EF_STATUS_CHECK_ERROR,       // unexpected status in check_context
  EF_STATUS_ASSERT_ERROR,      // error in assert formulas
  EF_STATUS_MDL_ERROR,         // error in model_from_map
  EF_STATUS_IMPLICANT_ERROR,   // error in get_implicant
  EF_STATUS_PROJECTION_ERROR,  // error in projection
  EF_STATUS_ERROR,             // any other internal error
} ef_status_t;

#define NUM_EF_STATUSES (EF_STATUS_ERROR+1)

/*
 * error_code below can be used for diagnostic
 * when status is EF_STATUS_..._ERROR:
 * - status = EF_STATUS_SUBST_ERROR
 *   error_code = negative code from apply_term_subst
 * - status = EF_STATUS_TVAL_ERROR
 *   error_code = not used (error from yices_term_array_value)
 * - status = EF_STATUS_CHECK_ERROR:
 *   error_code = the unexpected status
 * - status = EF_STATUS_ASSERT_ERROR
 *   error_code = exception code from context_assert_formulas
 */
typedef struct ef_solver_s {
  // Input problem + logic and architecture codes
  ef_prob_t *prob;
  smt_logic_t logic;
  context_arch_t arch;
  ef_status_t status;
  int32_t error_code;        // for diagnostic

  // Parameters used during the search
  const param_t *parameters; // search parameters
  ef_gen_option_t option;    // generalization mode
  uint32_t max_samples;      // bound on pre-sampling: 0 means no pre-sampling
  uint32_t max_iters;        // bound on outer iterations
  uint32_t iters;            // number of outer iterations
  uint32_t scan_idx;         // first universal constraint to check

  // Exists and forall contexts + exists model
  context_t *exists_context;
  context_t *forall_context;
  model_t *exists_model;
  term_t *evalue;
  term_t *uvalue;

  // Support for implicant construction and projection
  model_t *full_model;
  ivector_t implicant;
  ivector_t projection;

  // Auxiliary buffers
  ivector_t evalue_aux;
  ivector_t uvalue_aux;
  ivector_t all_vars;
  ivector_t all_values;

  // For verbose output (default = NULL)
  tracer_t *trace;
} ef_solver_t;



/*
 * Initialize solver:
 * - prob = problem descriptor
 * - logic/arch = for context initialization
 */
extern void init_ef_solver(ef_solver_t *solver, ef_prob_t *prob, smt_logic_t logic, context_arch_t arch);


/*
 * Delete the whole thing
 */
extern void delete_ef_solver(ef_solver_t *solver);


/*
 * Set the trace:
 * - the current tracer must be NULL.
 */
extern void ef_solver_set_trace(ef_solver_t *solver, tracer_t *trace);



/*
 * Check satisfiability:
 *
 * The result is stored in solver->status:
 * - EF_STATUS_ERROR if something goes wrong
 * - EF_STATUS_INTERRUPTED if one of the calls to check_context is interrupted
 * - EF_STATUS_UNSAT if all exists models have been tried and none of them worked
 * - EF_STATUS_UNKNOWN if the iteration limit is reached
 * - EF_STATUS_SAT if a good model is found
 *
 * In the later case,
 * - the model is stored in solver->exists_model
 * - also it's available as a mapping form solver->prob->evars to solver->evalues
 *
 * Also solver->iters stores the number of iterations required.
 */
extern void ef_solver_check(ef_solver_t *solver, const param_t *parameters,
			    ef_gen_option_t gen_mode, uint32_t max_samples, uint32_t max_iters);


/*
 * Stop the search
 */
extern void ef_solver_stop_search(ef_solver_t *solver);


/*
 * Print solution
 */
extern void print_ef_solution(FILE *f, ef_solver_t *solver);



#endif /* __EFSOLVER_H */
