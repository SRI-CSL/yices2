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
 * Given constraint
 *   (FORALL Y_i: B_i(Y_i) => C_i(X_i, Y_i))
 * we can sample y_s that satisfy B_i(Y_i). For every
 * such y_i, we get a constraint C_i(X_i, y_i) by substitution.
 * Then this constraint depends only on the existential
 * variable, so we can add (not (C_i(X_i, y_i))) to the
 * exists context.
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
#include <setjmp.h>

#include "yices_types.h"
#include "tracer.h"

#include "smt_logic_codes.h"
#include "search_parameters.h"
#include "context.h"
#include "ef_problem.h"



/*
 * OPERATION ON THE EXISTS CONTEXT
 */

/*
 * NOTE: operations from context.h can be applied to the exists and
 * forall context (including context_delete and add_blocking_clause)
 */

/*
 * Initialization:
 * - initialize ctx
 * - the context is configured based on logic and arch
 * - logic = logic code (NONE means purely Boolean)
 * - arch = solver architecture (as defined in context.h)
 * - the context's mode is set to MULTIPLECHECKS
 */
extern void init_ef_context(context_t *ctx, ef_prob_t *prob, smt_logic_t logic, context_arch_t arch);

/*
 * Assert all conditions defined in prob into ctx
 *
 * Return code (all codes are defined in context.h)
 * - TRIVIALLY_UNSAT means that an inconsistency is detected
 * - CTX_NO_ERROR means nothing bad happened
 * - otherwise the code is negative and indicates an error.
 */
extern int32_t exits_context_assert_conditions(context_t *ctx, ef_prob_t *prob);

/*
 * Upate: add one more assertion to ctx
 * - f must be a Boolean term
 * - return code: as above (check context.h)
 */
extern int32_t update_exists_context(context_t *ctx, term_t f);


/*
 * Assert (B and not C) in context ctx
 * - b and c must be two Boolean terms
 *
 * Return code (all codes are defined in context.h)
 * - TRIVIALLY_UNSAT means that an inconsistency is detected
 * - CTX_NO_ERROR means nothing bad happened
 * - otherwise the code is negative and indicates an error.
 */
extern int32_t forall_context_assert(context_t *ctx, term_t b, term_t c);



/*
 * CHECK SATISFIABILITY AND BUILD A MODEL
 * THIS CAN BE USED FOR BOTH EXISTS AND FORALL CONTEXTS
 */

/*
 * Check satisfiability and get a model
 * - ctx = the context
 * - parameters = heuristic settings (if parameters is NULL,
 *   the default settings are used)
 * - var = array of n uninterpreted terms
 * - value = array of n terms (to receive the value of each var)
 * - n = size of array evar and value
 *
 * The return code is as in check_context:
 * 1) if code = STATUS_SAT then the context is satisfiable
 *   and a model is stored in value[0 ... n-1]
 * - value[i] = a constant term mapped to evar[i] in the model
 * 2) code = STATUS_UNSAT: not satisfiable
 *
 * 3) other codes report an error of some kind
 */
extern smt_status_t satisfy_context(context_t *ctx, const param_t *parameters, term_t *var, term_t *value, uint32_t n);


/*
 * Try to get another model: add a blocking clause then call satisfy_context
 * again. Same return codes as satisfy_context
 */
extern smt_status_t recheck_context(context_t *ctx, const param_t *parameters, term_t *var, term_t *value, uint32_t n);


/*
 * SUBSTITUTION
 */

/*
 * - apply the substitution defined by var and value to term t
 * - n = size of arrays var and value
 * - return code < 0 means that an error occurred during the substitution
 *   (cf. apply_term_subst in term_substitution.h).
 */
extern term_t ef_substitution(ef_prob_t *prob, term_t *var, term_t *value, uint32_t n, term_t t);



/*
 * MODEL PROJECTION
 */

/*
 * Project model to a subset of the existential variables
 * - value[i] = exist model = array of constant values
 * - evar = an array of n existential variables: every element of evar occurs in ef->all_evar
 * - then this function projects builds the model restricted to evar into array eval
 *
 * Assumption:
 * - value[i] = value mapped to ef->all_evars[i] for i=0 ... num_evars-1
 * - every x in sub_var occurs somewhere in ef->all_evars
 * - then if evar[i] = x and x is equal to all_evar[k] the function copies
 *   value[k] into eval[i]
 */
extern void ef_project_exits_model(ef_prob_t *prob, term_t *value, term_t *evar, term_t *eval, uint32_t n);


/*
 * Same thing for a universal model:
 * - value[i] = model = array of constant value such that value[i] is the value of ef->all_uvar[i]
 * - uvar = subset of the universal variables (of size n)
 * - uval = restriction of value to uvar (as above)
 */
extern void ef_project_forall_model(ef_prob_t *prob, term_t *value, term_t *uvar, term_t *uval, uint32_t n);



/*
 * SUPPORT FOR GENERALIZATION
 */

/*
 * Option 1: build the formula (or (/= var[0] value[0]) ... (/= var[n-1] value[n-1]))
 */
extern term_t ef_generalize1(ef_prob_t *prob, term_t *var, term_t *value, uint32_t n);

/*
 * Option 2: assuming that we have a model for the universal constraint i in prob
 * - build the corresponding substitution to prob->cnstr[i].guarantee
 * - value = model for cnstr[i]: value[k] = what's mapped to cnstr[i].uvar[k] in the model
 */
extern term_t ef_generalize2(ef_prob_t *prob, uint32_t i, term_t *value);



/*
 * GLOBAL PROCEDURES
 */

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
} ef_gen_option_t;

typedef struct ef_solver_s {
  ef_prob_t *prob;
  const param_t *parameters;
  smt_logic_t logic;
  context_arch_t arch;
  ef_gen_option_t option;
  uint32_t max_samples; // for pre-sampling
  uint32_t iters;       // number of iterations
  smt_status_t status;
  int32_t code;
  uint32_t scan_idx;    // first universal constraint to check

  context_t *exists_context;
  context_t *forall_context;
  term_t *evalue;
  term_t *uvalue;
  ivector_t evalue_aux;
  ivector_t uvalue_aux;
} ef_solver_t;


/*
 * Initialize solver:
 * - prob = problem descriptor
 * - logic/arch/parameters = for context initialization and check
 * - option = generalization option
 * - max_samples = sampling setting
 */
extern void init_ef_solver(ef_solver_t *solver, ef_prob_t *prob, const param_t *parameters,
			   smt_logic_t logic, context_arch_t arch,
			   ef_gen_option_t option, uint32_t max_samples);

/*
 * Delete the whole thing
 */
extern void delete_ef_solver(ef_solver_t *solver);


/*
 * Increment the scan index
 */
extern void ef_scan_increment(ef_solver_t *solver);

/*
 * Initialize the exists context
 * - asserts all conditions from solver->prob
 * - if max_samples is positive, also apply pre-sampling to all the universal constraints
 * - return code:
 *   TRIVIALLY_UNSAT --> exists context is unsat (not ef solution)
 *   CTX_NO_ERROR --> nothing bad happened
 *   negative values --> errors (cf. context.h)
 */
extern int32_t ef_solver_start(ef_solver_t *solver);


/*
 * Start a new iteration: search for a model of the current exists context
 * - precondition: the exists context is allocated and ready (i.e.,
 *   ef_solver_start was called and returned CTX_NO_ERROR)
 * - return code:
 *   if STATUS_SAT (or STATUS_UNKNOWN): the model is stored in solver->evalue
 *   if STATUS_UNSAT: no model found (EF problem is unsat)
 *   anything else: error of some kind
 */
extern smt_status_t ef_solver_check_exists(ef_solver_t *solver);


/*
 * Test the current exists model using universal constraint i
 * - i must be a valid index (i.e., 0 <= i < solver->prob.num_cnstr)
 * - this checks the assertion B_i and not C_i after replacing existential
 *   variables by their values (stored in evalues)
 * - return code:
 *   if STATUS_SAT (or STATUS_UNKNOWN): a model of B_i and not C_i
 *   is found and stored in uvalue_aux
 *   if STATUS_UNSAT: not model found (current exists model is good as
 *   far as constraint i is concerned)
 *   anything else: an error
 */
extern smt_status_t ef_solver_check_forall(ef_solver_t *solver, uint32_t i);


/*
 * Learn a new constraint for the exists context from a forall witness
 * - i = index of the universal constraint for which we have a witness
 * - the witness is defined by the uvars of constraint i
 * + the values stored in uvalue_aux.
 * - this adds a constraint that will remove the current exists model
 * - if solver->option is EF_NOGEN_OPTION, the new constraint is
 *   of the form (or (/= var[0] eval[k0) ... (/= var[k-1] eval[k-1]))
 *   where var[0 ... k-1] are the exist variables of constraint i
 * - if solver->option is EF_GEN_BY_SUBST_OPTION, we build a new
 *   constraint by substitution (option 2)
 *
 * Return code:
 * - TRIVIALLY_UNSAT: the new constraint make exists_context unsat
 * - CTX_NO_ERROR: nothing bad happened
 * - a negative value --> error
 */
extern int32_t ef_solver_learn(ef_solver_t *solver, uint32_t i);


/*
 * Print model for the exists variables
 */
extern void print_ef_solution(FILE *f, ef_solver_t *solver);

/*
 * Show witness found for constraint i
 */
extern void print_forall_witness(FILE *f, ef_solver_t *solver, uint32_t i);

#endif /* __EFSOLVER_H */
