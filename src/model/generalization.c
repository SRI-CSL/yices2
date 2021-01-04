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

#include "model/generalization.h"
#include "model/model_queries.h"
#include "model/projection.h"
#include "model/val_to_term.h"
#include "terms/term_substitution.h"


/*
 * Split the array of variables v into discrete and real variables
 * - n = number of variables in v
 * - all variables of type REAL are added to vector reals
 * - all other variables are added to discretes
 */
static void split_elim_array(term_table_t *terms, uint32_t n, const term_t v[], ivector_t *reals, ivector_t *discretes) {
  uint32_t i;
  term_t t;

  for (i=0; i<n; i++) {
    t = v[i];
    if (is_real_term(terms, t)) {
      ivector_push(reals, t);
    } else {
      ivector_push(discretes, t);
    }
  }
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
  assert(MDL_EVAL_FORMULA_FALSE <= error && error <= MDL_EVAL_INTERNAL_ERROR);
  return error;
}

static inline int32_t gen_projection_error(proj_flag_t error) {
  assert(PROJ_ERROR_BAD_ARITH_LITERAL <= error && error <= PROJ_ERROR_NON_LINEAR);
  return error + (GEN_PROJ_ERROR_NON_LINEAR - PROJ_ERROR_NON_LINEAR);
}


/*
 * Generalization by substitution: core procedure
 * - mdl = model
 * - mngr = relevant term manager
 * - elim[0 ... nelim -1] = variables to eliminate
 * - on entry to the function, v must contain the formulas to project
 * - the result is returned in place (in vector v)
 *
 * - returned code: 0 if no error, an error code otherwise
 * - error codes are listed in generalization.h
 */
static int32_t gen_model_by_subst(model_t *mdl, term_manager_t *mngr, uint32_t nelims, const term_t elim[], ivector_t *v) {
  term_subst_t subst;
  ivector_t aux;
  term_table_t *terms;
  int32_t code;
  uint32_t k, n;
  term_t t;

  // get the value of elim[i] in aux.data[i]
  init_ivector(&aux, nelims);
  code = evaluate_term_array(mdl, nelims, elim, aux.data);
  if (code < 0) {
    // error in evaluator
    code = gen_eval_error(code);
    assert(GEN_EVAL_FAILED <= code  && code <= GEN_EVAL_INTERNAL_ERROR);
    goto done;
  }

  // convert every aux.data[i] to a constant term
  terms = term_manager_get_terms(mngr);
  k = convert_value_array(mngr, terms, model_get_vtbl(mdl), nelims, aux.data);
  if (k < nelims) {
    // aux.data[k] couldn't be converted to a term
    // the error code is in aux.data[k]
    code = gen_convert_error(aux.data[k]);
    assert(GEN_CONV_FAILED <= code && code <= GEN_CONV_INTERNAL_ERROR);
    goto done;
  }


  // build the substitution: elim[i] := aux.data[i]
  // then apply it to every term in vector v
  code = 0;
  init_term_subst(&subst, mngr, nelims, elim, aux.data);
  n = v->size;
  for (k=0; k<n; k++) {
    t = apply_term_subst(&subst, v->data[k]);
    v->data[k] = t;
    if (t < 0) {
      code = GEN_PROJ_ERROR_IN_SUBST;
      break;
    }
  }
  delete_term_subst(&subst);

 done:
  delete_ivector(&aux);

  return code;
}


/*
 * Generalization by projection: core procedure
 * - compute an implicant then project the implicant
 * - mdl = model
 * - mngr = relevant term manager
 * - elim[0 ... nelims-1] = variables to eliminate
 * - on entry to the function, v must contain the formulas to project
 *   the result is returned in place (in vector v)
 *
 * Return code: 0 if no error, an error code otherwise
 */
static int32_t gen_model_by_proj(model_t *mdl, term_manager_t *mngr, uint32_t nelims, const term_t elim[], ivector_t *v) {
  ivector_t implicant;
  int32_t code;
  proj_flag_t pflag;

  init_ivector(&implicant, 10);
  code = get_implicant(mdl, mngr, LIT_COLLECTOR_ALL_OPTIONS, v->size, v->data, &implicant);
  if (code < 0) {
    // implicant construction failed
    code = gen_implicant_error(code);
    goto done;
  }
  
  ivector_reset(v); // reset v to collect the projection result
  code = 0;
  pflag = project_literals(mdl, mngr, implicant.size, implicant.data, nelims, elim, v);
  if (pflag != PROJ_NO_ERROR) {
    code = gen_projection_error(pflag);
  }

 done:
  delete_ivector(&implicant);

  return code;
  
}



/*
 * Generalization by substitution
 * - mdl = model
 * - mngr = relevant term manager
 * - f[0 ... n-1] = formula true in the model
 * - elim[0 ... nelim -1] = variables to eliminate
 * - v = result vector
 *
 * - returned code: 0 if no error, an error code otherwise
 * - error codes are listed in generalization.h
 */
int32_t gen_model_by_substitution(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[], 
				  uint32_t nelims, const term_t elim[], ivector_t *v) {

  ivector_copy(v, f, n);
  assert(v->size == n);
  return gen_model_by_subst(mdl, mngr, nelims, elim, v);
}


/*
 * Generalize by projection:
 * - compute an implicant then project the implicant
 * - mdl = model
 * - mngr = relevant term manager
 * - f[0 ... n-1] = formulas true in mdl
 * - elim[0 ... nelims-1] = variables to eliminate
 * - v = result vector
 *
 * - returned code: 0 if no error, an error code otherwise
 * - error codes are listed in generalization.h
 */
int32_t gen_model_by_projection(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
				uint32_t nelims, const term_t elim[], ivector_t *v) {
  ivector_copy(v, f, n);
  assert(v->size == n);
  return gen_model_by_proj(mdl, mngr, nelims, elim, v);
}



/*
 * Generalize mdl: two passes:
 * - 1) eliminate the discrete variables by substitution
 * - 2) use projection to eliminate the real variables
 */
int32_t generalize_model(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
			 uint32_t nelims, const term_t elim[], ivector_t *v) {
  term_table_t *terms;
  ivector_t discretes;
  ivector_t reals;
  int32_t code;

  // if n == 0, there's nothing to do
  code =0;
  if (n > 0) {
    terms = term_manager_get_terms(mngr);
    init_ivector(&reals, 10);
    init_ivector(&discretes, 10);
    split_elim_array(terms, nelims, elim, &reals, &discretes);
   
    ivector_copy(v, f, n);
    if (discretes.size > 0) {
      code = gen_model_by_subst(mdl, mngr, discretes.size, discretes.data, v);
    }
    if (code == 0 && reals.size > 0) {
      code = gen_model_by_proj(mdl, mngr, reals.size, reals.data, v);
    }

    delete_ivector(&reals);
    delete_ivector(&discretes);
  }

  return code;
}

