/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
 * subsitution, Fourier-Motkin, and Virtual Term Subsitution (as
 * implemented in arith_projection).
 */

#ifndef __PROJECTION_H
#define __PROJECTION_H

#include <stdint.h>

#include "model/models.h"
#include "model/arith_projection.h"
#include "terms/term_manager.h"
#include "terms/elim_subst.h"
#include "terms/term_substitution.h"
#include "utils/int_vectors.h"


/*
 * Error flags
 */
typedef enum {
  PROJ_NO_ERROR = 0,
  PROJ_ERROR_IN_EVAL,
  PROJ_ERROR_IN_CONVERT,
} proj_flag_t;

/*
 * Projector data structure:
 * - keeps track of model + term manager + term table
 * - variables to eliminate are stored in array evars
 *   and in set vars_to_elim
 * - literals: contains a set of literals at different
 *   stages of the elimination process
 * - flag: either 0 or an error code
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
  ivector_t literals;

  // status flags
  int32_t flag;
  int32_t error_code;

  // generic buffer + auxiliary data structures
  ivector_t buffer;
  elim_subst_t *elim_subst;
  arith_projector_t *arith_proj;
  term_subst_t *val_subst;

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
 */
extern void projector_add_literal(projector_t *proj, term_t t);


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
 * Return code: 0 means no error
 */
extern int32_t project_literals(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t *a,
				uint32_t nvars, const term_t *var, ivector_t *v);


#endif /* __PROJECTION_H */
