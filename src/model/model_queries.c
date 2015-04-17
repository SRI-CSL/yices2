/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * QUERIES TO GET THE VALUE OF ONE OR MORE TERMS IN A MODEL
 */

#include "model/model_eval.h"
#include "model/model_queries.h"
#include "utils/memalloc.h"


/*
 * Get the value of t in mdl
 * - this function first tries a simple lookup in mdl. If that fails,
 *   it computes t's value in mdl (cf. model_eval.h).
 * - t must be a valid term
 *
 * Returns a negative number if t's value can't be computed
 *    -1  means that the value is not known
 *    other values are evaluation errors defined in model_eval.h
 *
 * Returns an index in mdl->vtbl otherwise (concrete value).
 */
value_t model_get_term_value(model_t *mdl, term_t t) {
  evaluator_t evaluator;
  value_t v;

  v = model_find_term_value(mdl, t);
  if (v == null_value) {
    init_evaluator(&evaluator, mdl);
    v = eval_in_model(&evaluator, t);
    delete_evaluator(&evaluator);
  }

  return v;
}


/*
 * Check whether f is true in mdl
 * - f must be a Boolean term
 * - this returns false if the evaluation fails and stores the error code in *code
 */
bool formula_holds_in_model(model_t *mdl, term_t f, int32_t *code) {
  value_t v;
  bool answer;

  assert(is_boolean_term(mdl->terms, f));

  answer = false;
  v = model_get_term_value(mdl, f);
  if (v < 0) {
    // evaluation error
    *code = v;    
  } else {
    *code = 0;
    answer = is_true(model_get_vtbl(mdl), v);
  }

  return answer;
}



/*
 * Compute the values of a[0 ... n-1] in mdl
 * - store the result in b[0 ... n-1]
 * - return a negative code if this fails for some a[i]
 * - return 0 otherwise.
 */
int32_t evaluate_term_array(model_t *mdl, uint32_t n, const term_t a[], value_t b[]) {
  evaluator_t evaluator;
  uint32_t i, k;
  value_t v;

  /*
   * First pass: simple eval of all terms.
   * - k = number of terms, for which this fails
   * - if simple eval fails for a[i], we have b[i] = null_value
   */
  k = 0;
  for (i=0; i<n; i++) {
    v = model_find_term_value(mdl, a[i]);
    b[i] = v;
    if (v < 0) {
      assert(v == null_value);
      k ++;
    }
  }

  /*
   * Second pass: if k > 0, use the evaluator to complete array b
   * Stop on the first error if any
   */
  if (k > 0) {
    init_evaluator(&evaluator, mdl);
    for (i=0; i<n; i++) {
      if (b[i] < 0) {
	v = eval_in_model(&evaluator, a[i]);
	b[i] = v;
	if (v < 0) break;
      }
    }
    delete_evaluator(&evaluator);
    if (v < 0) {
      return v;
    }
  }

  return 0;
}


/*
 * Checks whether mdl is a model of a[0 ... n-1]
 * - sets *code to 0 if the evaluation succeeds
 * - returns false if the evaluation fails for some a[i] and stores
 *   the corresponding error code in *code
 */
bool formulas_hold_in_model(model_t *mdl, uint32_t n, const term_t a[], int32_t *code) {
  evaluator_t evaluator;
  value_table_t *vtbl;
  uint32_t i;
  value_t v;
  bool answer;

  answer = true;
  *code = 0;

  vtbl = model_get_vtbl(mdl);
  init_evaluator(&evaluator, mdl);
  for (i=0; i<n; i++) {
    assert(is_boolean_term(mdl->terms, a[i]));
    v = eval_in_model(&evaluator, a[i]);
    if (v < 0) {
      answer = false;
      *code = v;
      break;
    }
    if (! is_true(vtbl, v)) {
      answer = false;
      break;
    }
  }
  delete_evaluator(&evaluator);

  return answer;    
}



