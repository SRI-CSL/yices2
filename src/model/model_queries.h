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

#ifndef __MODEL_QUERIES_H
#define __MODEL_QUERIES_H

#include <stdint.h>
#include <stdbool.h>

#include "model/models.h"


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
extern value_t model_get_term_value(model_t *mdl, term_t t);

/*
 * Compute the values of a[0 ... n-1] in mdl
 * - store the result in b[0 ... n-1]
 * - return a negative code if this fails for some a[i]
 * - return 0 otherwise.
 */
extern int32_t evaluate_term_array(model_t *mdl, uint32_t n, const term_t a[], value_t b[]);


/*
 * Checks whether f is true in mdl
 * - f must be a Boolean term
 * - code is set to 0, if the evaluation succeeds
 * - returns false if the evaluation fails and stores the error code in *code
 */
extern bool formula_holds_in_model(model_t *mdl, term_t f, int32_t *code);


/*
 * Checks whether mdl is a model of a[0 ... n-1]
 * - all terms in a must be Boolean
 * - sets *code to 0 if the evaluation succeeds
 * - returns false if the evaluation fails for some a[i] and stores
 *   the corresponding error code in *code
 */
extern bool formulas_hold_in_model(model_t *mdl, uint32_t n, const term_t a[], int32_t *code);


/*
 * Get a list of all variables that have a value in the model
 * - the variables are added to vector *v
 */
extern void model_get_relevant_vars(model_t *mdl, ivector_t *v);


/*
 * Collect the support of term t in model mdl
 * - the variables are added to vector *v
 * - the support of t is a set of variables x_1, ..., x_n
 *   such that the value of t in mdl is determined by the values
 *   of x_1, ..., x_n in mdl.
 */
extern void model_get_term_support(model_t *mdl, term_t t, ivector_t *v);


/*
 * Collect the support of terms a[0 ... n-1] in model mdl
 * - the variables are added to vector *v
 * - the support of t is a set of variables x_1, ..., x_n
 *   such that the values of a[0], ..., a[n] in mdl are determined by
 *   the value of x_1, ..., x_n in mdl.
 */
extern void model_get_terms_support(model_t *mdl, uint32_t n, const term_t  a[], ivector_t *v);


#endif /* __MODEL_QUERIES_H */
