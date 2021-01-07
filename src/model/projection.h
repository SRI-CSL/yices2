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
 * PROJECTION OF A CONJUNCTION OF LITERALS USING A MODEL
 *
 * Given a conjunction of literals C = L_1 ... L_n, a model M for
 * these literals, and a set of variables Y, this module constructs a
 * cube D by eliminating the variables Y from C.
 *
 * D satisfies the following properties:
 * - D is true in M
 * - no variables of Y occur in D
 * - D => (EXISTS Y. C) is valid.
 *
 * The quantifier elimination is based on substitution (for Boolean
 * variables) and on arithmetic elimination using a mix of
 * substitution, Fourier-Motkin, and Virtual Term Substitution (as
 * implemented in arith_projection).
 */

#ifndef __PROJECTION_H
#define __PROJECTION_H

#include <stdint.h>

#include "model/arith_projection.h"
#include "model/presburger.h"
#include "model/models.h"
#include "terms/elim_subst.h"
#include "terms/term_manager.h"
#include "terms/term_substitution.h"
#include "utils/int_vectors.h"


/*
 * Error flags
 */
typedef enum {
  PROJ_NO_ERROR = 0,
  PROJ_ERROR_NON_LINEAR = -1,
  PROJ_ERROR_IN_EVAL = -2,
  PROJ_ERROR_IN_CONVERT = -3,
  PROJ_ERROR_IN_SUBST = -4,
  PROJ_ERROR_BAD_ARITH_LITERAL = -5,
  PROJ_ERROR_BAD_PRESBURGER_LITERAL = -6,
} proj_flag_t;


/*
 * Projector data structure:
 * - keeps track of model + term manager + term table
 * - variables to eliminate are stored in array evars
 *   and in set vars_to_elim
 * - we keep the set of literals to process in two vectors:
 *     arith_literals = arithmetic literals
 *     gen_literals = everything else
 * - for arithmetic literals, we must collect the arithmetic
 *   variables to keep. We store them in set avars_to_keep
 *   and vector arith_vars.
 *
 * To report errors/exceptions:
 * - flag: one of the proj_flag status defined above
 *   error_code: an extra integer to help diagnosis
 *
 * Auxiliary data structures (allocated when needed).
 * - elim_subst: eliminate Boolean/bitvector variables by substitution
 * - arith_proj: to eliminate arithmetic variables
 * - val_subst: to eliminate whatever is left (replace Y by its value
 *   in the model).
 */
typedef struct projector_s {
  model_t *mdl;
  term_manager_t *mngr;
  term_table_t *terms;

  // variables to eliminate
  int_hset_t vars_to_elim;
  term_t *evars;
  uint32_t num_evars;

  // literals to process
  ivector_t gen_literals;
  ivector_t arith_literals;

  // arithmetic variables
  int_hset_t *avars_to_keep; // NULL by default, allocated if needed
  ivector_t arith_vars;

  // status flags
  int32_t flag;
  int32_t error_code;

  // generic buffer + auxiliary data structures
  ivector_t buffer;
  elim_subst_t *elim_subst;
  arith_projector_t *arith_proj;
  term_subst_t *val_subst;

  // cooper playground
  bool is_presburger;
  presburger_t *presburger;

  // nonlinear arithmetic
  bool is_nonlinear;

} projector_t;


#define MAX_PROJ_EVARS_SIZE ((uint32_t) (UINT32_MAX/sizeof(term_t)))

/*
 * Initialize projector:
 * - nvars/vars = variables to eliminate
 * - makes an internal copy of vars
 * - the literals vector is empty
 */
extern void init_projector(projector_t *proj, model_t *mdl, term_manager_t *mngr, 
			   uint32_t nvars, const term_t *var);


/*
 * Delete: free memory
 */
extern void delete_projector(projector_t *proj);


/*
 * Add literal t to the projector
 * - t must be true in the model
 * - sets proj->flag to PROJ_ERROR_NON_LINEAR if t is a non-linear constraint
 *   (e.g., t is p >= 0 or p == 0 where p is non-linear).
 */
extern void projector_add_literal(projector_t *proj, term_t t);


/*
 * Process the literals: eliminate the variables
 * - the result is a  set of literals that don't contain
 *   the variables to eliminate
 * - these literals are added to vector *v
 * - v is not reset
 *
 * The function returns an error code if something goes wrong
 * and leaves v untouched. Otherwise, it returns PROJ_NO_ERROR.
 */
extern proj_flag_t run_projector(projector_t *proj, ivector_t *v);


/*
 * Eliminate variables var[0 ... nvars-1] from the cube
 * defined by a[0] ... a[n-1].
 * - mdl = model that satisfies all literals a[0 ... n-1]
 * - mngr = term manager such that mngr->terms == mdl->terms
 * - the result is added to vector v (v is not reset)
 *
 * The terms in a[0 ... n-1] must all be arithmetic/bitvectors
 * or Boolean literals. (A Boolean literal is either (= p q) or
 * (not (= p q)) or p or (not p), where p and q are Boolean terms).
 *
 * Return code: same as run_projector.
 */
extern proj_flag_t project_literals(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t *a,
				    uint32_t nvars, const term_t *var, ivector_t *v);


#endif /* __PROJECTION_H */
