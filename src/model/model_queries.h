/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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



#endif /* __MODEL_QUERIES_H */
