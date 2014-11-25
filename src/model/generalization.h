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

#ifndef __GENERALIZATION_H
#define __GENERALIZATION_H

#include <stdint.h>

#include "model/models.h"
#include "terms/term_manager.h"

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
extern term_t generalize_model(model_t *mdl, uint32_t n, const term_t f[], uint32_t nelims, const term_t elim[]);


#endif /* __GENERALIZATION_H */
