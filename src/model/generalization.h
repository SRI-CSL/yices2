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
 *
 * Two projection variants are exposed:
 *
 * - "wide" (the default for the public API): walks the Boolean
 *   structure of F(x, y) and unions per-disjunct projections, so
 *   that G(x) is strictly broader than the sign-invariant cell of
 *   one chosen implicant whenever F has Boolean structure the model
 *   satisfies in more than one way. Wider output, slightly more
 *   expensive per call. Recommended for CEGAR-style outer loops
 *   over quantifier prefixes (exists/forall, QSMA, etc.).
 *
 * - "local": the legacy pipeline. Computes a single implicant of F
 *   at the model (one literal per disjunct), then projects that flat
 *   conjunction. Cheaper per call but commits to one disjunct, so the
 *   resulting cell is narrower whenever F has Boolean structure.
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
  GEN_PROJ_ERROR_BAD_PRESBURGER_LITERAL = -19,
  GEN_PROJ_ERROR_UNSUPPORTED_ARITH_TERM = -20,
};


/*
 * Generalize mdl:
 * - f[0 ... n-1] = array of n Boolean formulas. They must all be true in mdl
 * - elim[0 ... nelims-1] = array of nelims terms (variables to eliminate)
 *   these are the Y variables. Any other variable of f[0 ... n-1] is considered
 *   as a variable to keep (i.e., an X variable).
 * - the generalization is returned in vector v (v is not reset, 
 *   the result formulas are added to v)
 * - extra_error: to help diagnose errors if something breaks.
 *
 * There are several variants:
 * - gen_model_by_substitution:
 *   replace every elim[i] by its value in the model.
 * - gen_model_by_projection:
 *   "wide" projection (the new default for the public API): builds a
 *   polarity-aware Boolean abstraction of f[], enumerates model-true
 *   Boolean implicants with a SAT solver and blocker clauses, projects
 *   each implicant via Loos-Weispfenning / Cooper / arith_proj, and
 *   unions the results at the term level. The cube_budget argument
 *   caps the number of SAT iterations (extracted+attempted cubes,
 *   whether or not projection succeeds); pass 0 for unbounded (the
 *   underlying Boolean enumeration is always finite).
 * - gen_model_by_projection_local:
 *   legacy projection. Builds a single literal implicant of f[] at the
 *   model and projects that flat conjunction. This is the algorithm Yices
 *   has used historically.
 * - generalize_model:
 *   the generic form (the public default, YICES_GEN_DEFAULT). Applies
 *   substitution for discrete variables and the legacy projection
 *   (gen_model_by_projection_local) for real variables. Callers who
 *   want the SAT-guided wide projection in the real-var pass must
 *   call gen_model_by_projection directly (or use the public
 *   YICES_GEN_BY_PROJ_WIDE mode).
 *
 * If a projection-based call fails and returns GEN_PROJ_ERROR_UNSUPPORTED_ARITH_TERM,
 * *extra_error stores the term_kind of the bad terms (see projection.h).
 */
extern int32_t gen_model_by_substitution(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
					 uint32_t nelims, const term_t elim[], ivector_t *v);

extern int32_t gen_model_by_projection(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
				       uint32_t nelims, const term_t elim[], ivector_t *v,
				       uint32_t cube_budget, int32_t *extra_error);

extern int32_t gen_model_by_projection_local(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
					     uint32_t nelims, const term_t elim[], ivector_t *v, int32_t *extra_error);

extern int32_t generalize_model(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
				uint32_t nelims, const term_t elim[], ivector_t *v,
				int32_t *extra_error);



#endif /* __GENERALIZATION_H */
