/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PROJECTION OF A SET OF LITERALS USING A MODEL
 */

#include <assert.h>
#include <stdbool.h>

#include "utils/memalloc.h"
#include "terms/term_sets.h"
#include "model/arith_projection.h"
#include "model/projection.h"
#include "model/model_queries.h"
#include "model/val_to_term.h"


#ifndef NDEBUG
// check whether x is a variable
static bool term_is_unint(term_table_t *terms, term_t x) {
  return is_pos_term(x) && term_kind(terms, x) == UNINTERPRETED_TERM;
}

static bool all_unint_terms(term_table_t *terms, uint32_t nvars, const term_t *var) {
  uint32_t i;

  for (i=0; i<nvars; i++) {
    if (! term_is_unint(terms, var[i])) {
      return false;
    }
  }
  return true;
}

// check whether x is true in proj->mdl
static bool true_formula(projector_t *proj, term_t t) {
  int32_t code;

  return good_term(proj->terms, t) && 
    is_boolean_term(proj->terms, t) &&
    formula_holds_in_model(proj->mdl, t, &code);
}
#endif


/*
 * Initialize projector:
 * - mdl and mngr: relevant model and term manager
 * - var[0 ... nvars-1] = variables to eliminate
 * - every var[i] must be an uninterpreted term
 */
void init_projector(projector_t *proj, model_t *mdl, term_manager_t *mngr, uint32_t nvars, const term_t *var) {  
  term_t *tmp;
  uint32_t i;

  assert(all_unint_terms(term_manager_get_terms(mngr), nvars, var));

  if (nvars > MAX_PROJ_EVARS_SIZE) {
    out_of_memory();
  }
  tmp = (term_t *) safe_malloc(nvars * sizeof(term_t));
  for (i=0; i<nvars; i++) {
    tmp[i] = var[i];
  }

  proj->mdl = mdl;
  proj->mngr = mngr;
  proj->terms = term_manager_get_terms(mngr);
  init_term_set(&proj->vars_to_elim, nvars, var);
  proj->evars = tmp;
  proj->num_evars = nvars;
  init_ivector(&proj->literals, 10);

  proj->flag = PROJ_NO_ERROR;
  proj->error_code = 0;

  init_ivector(&proj->buffer, 10);
  proj->elim_subst = NULL;
  proj->arith_proj = NULL;
  proj->val_subst = NULL;
}


/*
 * Allocate and initialize elim_subst
 */
static void proj_build_elim_subst(projector_t *proj) {
  elim_subst_t *tmp;

  assert(proj->elim_subst == NULL);

  tmp = (elim_subst_t *) safe_malloc(sizeof(elim_subst_t));
  init_elim_subst(tmp, proj->mngr, &proj->vars_to_elim);
  proj->elim_subst = tmp;
}


/*
 * Allocate and initialize arith_proj
 * - use default sizes
 * - no variables are added to arith_proj
 */
static void proj_build_arith_proj(projector_t *proj) {
  arith_projector_t *tmp;

  assert(proj->arith_proj == NULL);

  tmp = (arith_projector_t *) safe_malloc(sizeof(arith_projector_t));
  init_arith_projector(tmp, proj->mngr, 0, 0);
  proj->arith_proj = tmp;
}


/*
 * Allocate and initialize val_subst:
 * - scan all variables in proj->evars
 * - compute their value in the model then build the substitution
 * - if something goes wrong, store an error code in proj->flag and leave 
 *   proj->val_subst NULL
 * 
 * Side effect: use proj->buffer
 */
static void proj_build_val_subst(projector_t *proj) {
  term_subst_t *tmp;
  ivector_t *v;
  uint32_t n, m;
  int32_t code;

  assert(proj->val_subst == NULL);

  n = proj->num_evars;
  v = &proj->buffer;
  resize_ivector(v, n);

  code = evaluate_term_array(proj->mdl, n, proj->evars, v->data);
  if (code < 0) {
    // error in evaluation:
    proj->flag = PROJ_ERROR_IN_EVAL;
    proj->error_code = code;
    return;
  }

  // convert v->data[0 ... n-1] to constant terms
  m = convert_value_array(proj->terms, model_get_vtbl(proj->mdl), n, v->data);
  assert(m <= n);
  if (m < n) {
    proj->flag = PROJ_ERROR_IN_CONVERT;
    proj->error_code = 0; // no subcode here
    return;
  }

  // build the subsitution: evar[i] is mapped to v->data[i]
  tmp = (term_subst_t *) safe_malloc(sizeof(term_subst_t));
  init_term_subst(tmp, proj->mngr, n, proj->evars, v->data);
  proj->val_subst = tmp;
}


/*
 * Delete: free memory
 */
static void proj_delete_elim_subst(projector_t *proj) {
  if (proj->elim_subst != NULL) {
    delete_elim_subst(proj->elim_subst);
    safe_free(proj->elim_subst);
    proj->elim_subst = NULL;
  }
}

static void proj_delete_arith_proj(projector_t *proj) {
  if (proj->arith_proj != NULL) {
    delete_arith_projector(proj->arith_proj);
    safe_free(proj->arith_proj);
    proj->arith_proj = NULL;
  }
}

static void proj_delete_val_subst(projector_t *proj) {
  if (proj->val_subst != NULL) {
    delete_term_subst(proj->val_subst);
    safe_free(proj->val_subst);
    proj->val_subst = NULL;
  }

}

void delete_projector(projector_t *proj) {
  delete_term_set(&proj->vars_to_elim);
  safe_free(proj->evars);
  proj->evars = NULL;
  delete_ivector(&proj->literals); 
  delete_ivector(&proj->buffer);

  proj_delete_elim_subst(proj);
  proj_delete_arith_proj(proj);
  proj_delete_val_subst(proj);
}



/*
 * Add a literal t to proj->literals
 */
void projector_add_literal(projector_t *proj, term_t t) {
  assert(true_formula(proj, t));
  ivector_push(&proj->literals, t);
}


/*
 * First pass in model-based projection:
 * - remove variables by substitution
 * - var = variables to eliminate
 * - nvars = size of array vars
 * - input = vector of literals
 */
static void projector_elim_by_substitution(projector_t *proj) {
  elim_subst_t *subst;
  uint32_t i, j, n;
  term_t t, x;

  proj_build_elim_subst(proj);
  subst = proj->elim_subst;

  // Build a substitution
  n = proj->literals.size;
  for (i=0; i<n; i++) {
    t = proj->literals.data[i];
    (void) elim_subst_try_cheap_map(subst, t, false);
  }
  elim_subst_remove_cycles(subst);

  // Remove all evars that are mapped by subst
  n = proj->num_evars;
  j = 0;
  for (i=0; i<n; i++) {
    x = proj->evars[i];
    t = elim_subst_get_map(subst, x);
    if (t < 0) { 
      // x is not eliminated by subst
      proj->evars[j] = x;
      j ++;
    }
  }
  proj->num_evars = j;

  // Apply the substitution to all literals
  if (j < n) {
    n = proj->literals.size;
    j = 0;
    for (i=0; i<n; i++) {
      t = elim_subst_apply(subst, proj->literals.data[i]);
      if (t != true_term) {
	// keep t
	proj->literals.data[j] = t;
	j ++;
      }
    }
    ivector_shrink(&proj->literals, j);
  }

  // Clean-up
  proj_delete_elim_subst(proj);
}


