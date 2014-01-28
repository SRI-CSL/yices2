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
 * Baseline implementation
 * -----------------------
 * - support Option 1 and 2.
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
#include "ef_problem.h"



/*
 * OPERATION ON THE EXISTS CONTEXT
 */

/*
 * NOTE: operations from context.h can be applied to the exists context
 * - including context_delete
 */

/*
 * Initialization:
 * - initialize ctx
 * - the context is configured based on logic and arch
 * - logic = logic code (NONE means purely Boolean)
 * - arch = solver architecture (as defined in context.h)
 */
extern void init_exists_context(context_t *ctx, ef_prob_t *prob, smt_logic_t logic, context_arch_t arch);

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
 * OPERATION ON A UNIVERSAL CONSTRAINT
 */

/*
 * Initialize a forall context:
 * - prob = the ef_problem
 * - logic and arch define the logic and solver architecture
 */
extern void init_forall_context(context_t *ctx, ef_prob_t *prob, smt_logic_t logic, context_arch_t arch);

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


#endif /* __EFSOLVER_H */
