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

#include "model/literal_collector.h"
#include "model/model_eval.h"
#include "model/models.h"
#include "model/projection.h"
#include "model/val_to_term.h"
#include "terms/term_manager.h"

/*
 * Error codes
 * - generalization by substitution can fail with an error code from model_eval
 *   or from val_to_term
 * - generalization by projection can fail with an error code from model_eval
 *   or with code = MDL_EVAL_FORMULA_FALSE (-8)
 * - we group and renumber these error codes here
 * - since NULL_TERM is -1, we start with -2
 */
enum {
  // evaluation errors (cf. model_eval.h)
  GEN_EVAL_INTERNAL_ERROR = -2,
  GEN_EVAL_UNKNOWN_TERM = -3,
  GEN_EVAL_FREEVAR_IN_TERM = -4,
  GEN_EVAL_QUANTIFIER = -5,
  GEN_EVAL_LAMBDA = -6,
  GEN_EVAL_FAILED = -7,

  // implicant error (cf. literal_collector.h)
  GEN_EVAL_FORMULA_FALSE = -8,

  // conversion errors (cf. val_to_term.h)
  GEN_CONV_INTERNAL_ERROR = -9,
  GEN_CONV_UNKNOWN_VALUE = -10,
  GEN_CONV_NOT_PRIMITIVE = -11,
  GEN_CONV_FUNCTION = -12,
  GEN_CONV_FAILED = -13,

  // projector error (cf. projection.h)
  GEN_PROJ_ERROR_NON_LINEAR = -14,
  GEN_PROJ_ERROR_IN_EVAL = -15,
  GEN_PROJ_ERROR_IN_CONVERT = -16,
  GEN_PROJ_ERROR_IN_SUBST = -17,
  GEN_PROJ_ERROR_BAD_ARITH_LITERAL = -18,
};


/*
 * Generalize mdl:
 * - f[0 ... n-1] = array of n Boolean formulas. They must all be true in mdl
 * - elim[0 ... nelims-1] = array of nelims terms (variables to eliminate)
 *   these are the Y variables. Any other variable of f[0 ... n-1] is considered
 *   as a variable to keep (i.e., an X variable).
 * - the generalization is returned in vector v (v is not reset, 
 *   the result formulas are added to v)
 *
 * There are two main variants for generalization by substitution or by projection
 * - the generic form: generalize_model applies generalization by projection
 *   if some variables to eliminate are arithmetic variables. It uses
 *   generalization by substitution otherwise.
 */
extern int32_t gen_model_by_substitution(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
					 uint32_t nelims, const term_t elim[], ivector_t *v);

extern int32_t gen_model_by_projection(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
				       uint32_t nelims, const term_t elim[], ivector_t *v);

extern int32_t generalize_model(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
				uint32_t nelims, const term_t elim[], ivector_t *v);



#endif /* __GENERALIZATION_H */
