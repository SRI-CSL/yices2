/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * MODEL GENERALIZATION
 *
 * Given a model mdl for a formula F(x, y), this module computes
 * the generalization of mdl for the variables 'x'. The result
 * is a formula G(x) such that 
 * 1) G(x) is true in mdl
 * 2) G(x) implies (EXISTS y: F(x, y))
 *
 * If any variable in y is an arithmetic variable then G(x) is
 * computed using model-based projection. Otherwise, G(x) is
 * obtained by substitution: we replace every variable y_i
 * by its value in the model.
 *
 * NOTE: we could use model-based projection in both cases, but
 * experiments with the exists/forall solver seem to show that
 * substitution works better for Boolean and bitvector variables.
 */

#include <assert.h>

#include "model/projection.h"
#include "model/generalization.h"
#include "model/model_queries.h"
#include "model/val_to_term.h"
#include "terms/term_substitution.h"


/*
 * Check whether one term in v[0 ... n-1] has arithmetic type
 */
static bool array_has_arith_term(term_table_t *terms, uint32_t n, const term_t v[]) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (is_arithmetic_term(terms, v[i])) {
      return true;
    }
  }
  return false;
}


/*
 * Conversion of error codes to GEN.. codes
 * - eval_errors are in the range [-7 ... -2]
 *   MDL_EVAL_FAILED = -7 and MDL_EVAL_INTERNAL_ERROR = -2
 *   they are kept unchanged
 * - conversion errors are in the range [-6 .. -2]
 *   CONVERT_FAILED = -6 and CONVERT_INTERNAL_ERROR = -2
 *   we renumber them to [-13 .. -9]
 * - implicant construction errors are in the range [-8 ... -2]
 *   MDL_EVAL_FORMULA_FALSE = -8 and MDL_EVAL_INTERNAL_ERROR = -2
 * - projection errors are in the range -1 to -5
 *   we renumber to [-18 .. -14]
 */
static inline int32_t gen_eval_error(int32_t error) {
  assert(MDL_EVAL_FAILED <= error && error <= MDL_EVAL_INTERNAL_ERROR);
  return error;
}

static inline int32_t gen_convert_error(int32_t error) {
  assert(CONVERT_FAILED <= error && error <= CONVERT_INTERNAL_ERROR);
  return error + (GEN_CONV_INTERNAL_ERROR - CONVERT_INTERNAL_ERROR);
}

static inline int32_t gen_implicant_error(int32_t error) {
  assert(MDL_EVAL_FAILED <= error && error <= MDL_EVAL_FORMULA_FALSE);
  return error;
}

static inline int32_t gen_projection_error(proj_flag_t error) {
  assert(PROJ_ERROR_NON_LINEAR <= error && error <= PROJ_ERROR_BAD_ARITH_LITERAL);
  return error + (GEN_PROJ_ERROR_NON_LINEAR - PROJ_ERROR_NON_LINEAR);
}


/*
 * Generalization by substitution
 * - mdl = model
 * - mngr = relevant term manager
 * - f = formula true in the model
 * - v[0 ... n -1] = variables to eliminate
 */
static term_t gen_model_by_substitution(model_t *mdl, term_manager_t *mngr, term_t f, uint32_t n, const term_t v[]) {
  term_subst_t subst;
  ivector_t aux;
  term_table_t *terms;
  int32_t code;
  uint32_t k;
  term_t result;

  // get the value of every v[i] in aux.data[i]
  init_ivector(&aux, n);
  code = evaluate_term_array(mdl, n, v, aux.data);
  if (code < 0) {
    // error in evaluator
    result = gen_eval_error(code);
    assert(GEN_EVAL_FAILED <= result && result <= GEN_EVAL_INTERNAL_ERROR);
    goto done;
  }

  // convert every aux.data[i] to a constant term
  terms = term_manager_get_terms(mngr);
  k = convert_value_array(terms, model_get_vtbl(mdl), n, aux.data);
  if (k < n) {
    // aux.data[k] couldn't be converted to a term
    // conversion error code is in aux.data[k]
    result = gen_convert_error(aux.data[k]);
    assert(GEN_CONV_FAILED <= result && result <= GEN_CONV_INTERNAL_ERROR);
    goto done;
  }

  // build the substition: v[i] is replaced by aux.data[i]
  init_term_subst(&subst, mngr, n, v, aux.data);
  result = apply_term_subst(&subst, f);
  delete_term_subst(&subst);

 done:
  delete_ivector(&aux);

  return result;
}


/*
 * Generalize by projection:
 * - compute an implicant then project the implicant
 * - mdl = model
 * - mngr = relevant term manager
 * - f[0 ... n-1] = formulas true in mdl
 * - elim[0 ... nelims-1] = variables to eliminate
 */
static term_t gen_model_by_projection(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
				      uint32_t nelims, const term_t elim[]) {
  ivector_t implicant;
  ivector_t projection;
  int32_t code;
  term_t result;
  proj_flag_t pflag;

  init_ivector(&implicant, 10);
  init_ivector(&projection, 10);

  code = get_implicant(mdl, mngr, LIT_COLLECTOR_ALL_OPTIONS, n, f, &implicant);
  if (code < 0) {
    // implicant construction failed
    result = gen_implicant_error(code);
    goto done;
  }
 
  assert(projection.size == 0);
  pflag = project_literals(mdl, mngr, implicant.size, implicant.data, nelims, elim, &projection);
  if (pflag != PROJ_NO_ERROR) {
    result = gen_projection_error(pflag);
    goto done;
  }

  // build the conjunct of projection.data
  if (projection.size == 0) {
    result = true_term;
  } else {
    result = mk_and(mngr, projection.size, projection.data);
  }
  
 done:
  delete_ivector(&projection);
  delete_ivector(&implicant);

  return result;
}



/*
 * Generalize mdl:
 * - f[0 ... n-1] = array of n Boolean formulas. They must all be true in mdl
 * - elim[0 ... nelims-1] = array of nelims terms (variables to eliminate)
 *   these are the Y variables. Any other variable of f[0 ... n-1] is considered
 *   as a variable to keep (i.e., an X variable).
 *
 * - return a formula G in which variables elim[0 ... nelims-1] do not occur
 *   and G implies (f[0] /\ ... /\ f[n-1])
 */
term_t generalize_model(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[], uint32_t nelims, const term_t elim[]) {
  term_table_t *terms;
  term_t result, fmla;

  terms = term_manager_get_terms(mngr);
  if (n > 0) {
    // we deal with n==0 separately since mk_and_safe requires n>0
    if (array_has_arith_term(terms, nelims, elim)) {
      result = gen_model_by_projection(mdl, mngr, n, f, nelims, elim);
    } else {
      fmla = mk_and_safe(mngr, n, f);
      result = gen_model_by_substitution(mdl, mngr, fmla, nelims, elim);
    }
  } else {
    // n == 0
    result = true_term;
  }

  return result;
}

