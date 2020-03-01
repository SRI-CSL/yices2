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
 * QUERIES TO GET THE VALUE OF ONE OR MORE TERMS IN A MODEL
 */

#include "model/model_eval.h"
#include "model/model_queries.h"
#include "model/model_support.h"
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



/*
 * Filter used below:
 * - aux is a term table
 * - t is relevant if it's uninterpreted and has a name
 */
static bool term_is_relevant(void *aux, term_t t) {
  return is_pos_term(t) && term_kind(aux, t) == UNINTERPRETED_TERM && term_name(aux, t) != NULL;
}

/*
 * Get a list of all variables that have a value in the model
 * - these variables are store into vector *v
 */
void model_get_relevant_vars(model_t *mdl, ivector_t *v) {
  evaluator_t eval;

  ivector_reset(v);
  if (mdl->has_alias && mdl->alias_map != NULL) {
    init_evaluator(&eval, mdl);

    /*
     * We use two passes to find all relevant terms:
     * 1) in the first pass, we compute the value of all terms
     *    in the model's alias table.
     * 2) in the second pass, we collect all terms that have
     *    received a value in the first pass.
     *
     * This is necessary in situations like this:
     *   (assert (= x  (.. y ..)))
     * and y does not occur anywhere else.
     * During model construction, we store [x --> (... y ...)]
     * in the model's alias table (so x is known to be relevant).
     * When we compute x's value in phase 1, we also assign a value
     * to y so y is relevant, and its value must be printed.
     *
     * The second pass makes sure that y is found.
     */
    model_collect_terms(mdl, true, mdl->terms, term_is_relevant, v);

    // compute their values
    eval_terms_in_model(&eval, v->data, v->size);

    // second pass: collect all uninterpreted terms that
    // have a value in model or in the evaluator.
    ivector_reset(v);
    model_collect_terms(mdl, false, mdl->terms, term_is_relevant, v);
    evaluator_collect_cached_terms(&eval, mdl->terms, term_is_relevant, v);
    delete_evaluator(&eval);

  } else {
    model_collect_terms(mdl, false, mdl->terms, term_is_relevant, v);
  }
}

/*
 * Copy content of harray_t *s into vector v
 */
static inline void copy_harray_to_vector(const harray_t *s, ivector_t *v) {
  assert(s != NULL);
  ivector_copy(v, s->data, s->nelems);
}

/*
 * Collect the support of term t in model mdl
 * - the variables are added to vector *v
 * - the support of t is a set of variables x_1, ..., x_n
 *   such that the value of t in mdl is determined by the values
 *   of x_1, ..., x_n in mdl.
 */
void model_get_term_support(model_t *mdl, term_t t, ivector_t *v) {
  support_constructor_t sup;
  harray_t *s;

  init_support_constructor(&sup, mdl);
  s = get_term_support(&sup, t);
  copy_harray_to_vector(s, v);
  delete_support_constructor(&sup);
}


/*
 * Collect the support of terms a[0 ... n-1] in model mdl
 * - the variables are added to vector *v
 * - the support of t is a set of variables x_1, ..., x_n
 *   such that the values of a[0], ..., a[n] in mdl are determined by
 *   the value of x_1, ..., x_n in mdl.
 */
void model_get_terms_support(model_t *mdl, uint32_t n, const term_t  a[], ivector_t *v) {
  support_constructor_t sup;
  harray_t *s;

  init_support_constructor(&sup, mdl);
  s = get_term_array_support(&sup, a, n);
  copy_harray_to_vector(s, v);
  delete_support_constructor(&sup);
}
