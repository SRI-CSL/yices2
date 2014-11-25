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
    goto done;
  }

  // convert every aux.data[i] to a constant term
  terms = term_manager_get_terms(mngr);
  k = convert_value_array(terms, model_get_vtbl(mdl), n, aux.data);
  if (k < n) {
    // aux.data[k] couldn't be converted to a term
    code = aux.data[k]; // error code stored there
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
