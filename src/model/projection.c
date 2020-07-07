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
 * PROJECTION OF A SET OF LITERALS USING A MODEL
 */

#include <assert.h>
#include <stdbool.h>

#include "model/arith_projection.h"
#include "model/model_queries.h"
#include "model/projection.h"
#include "model/presburger.h"
#include "model/val_to_term.h"
#include "terms/term_sets.h"
#include "utils/memalloc.h"

#define TRACE 0

#if TRACE
#include <inttypes.h>
#include "io/term_printer.h"
#endif

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
 * Report an error: set flag/code unless they already contain
 * an error status.
 */
static void proj_error(projector_t *proj, proj_flag_t flag, int32_t code) {
  assert(flag != PROJ_NO_ERROR);
  if (proj->flag == PROJ_NO_ERROR) {
    proj->flag = flag;
    proj->error_code = code;
  }
}


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

  init_ivector(&proj->gen_literals, 0);
  init_ivector(&proj->arith_literals, 0);

  proj->avars_to_keep = NULL;
  init_ivector(&proj->arith_vars, 0);

  proj->flag = PROJ_NO_ERROR;
  proj->error_code = 0;

  init_ivector(&proj->buffer, 10);
  proj->elim_subst = NULL;
  proj->arith_proj = NULL;
  proj->val_subst = NULL;

  proj->is_presburger = true;  
  proj->presburger = NULL;
}


/*
 * Get the set of arithmetic variables to keep
 */
static int_hset_t *proj_get_avars_to_keep(projector_t *proj) {
  int_hset_t *tmp;

  tmp = proj->avars_to_keep;
  if (tmp == NULL) {
    tmp = (int_hset_t *) safe_malloc(sizeof(int_hset_t));
    init_int_hset(tmp, 0);
    proj->avars_to_keep = tmp;
  }
  return tmp;
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
 * Allocate and initialize presburger projector
 * - use default sizes
 * - no variables are added to the projector
 */
static void proj_build_presburger_proj(projector_t *proj) {
  presburger_t *tmp;

  assert(proj->presburger == NULL);

  tmp = (presburger_t *) safe_malloc(sizeof(presburger_t));
  init_presburger_projector(tmp, proj->mngr, 0, 0);
  proj->presburger = tmp;
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
    // error in evaluation
    proj_error(proj, PROJ_ERROR_IN_EVAL, code);
    return;
  }

  // convert v->data[0 ... n-1] to constant terms
  m = convert_value_array(proj->mngr, proj->terms, model_get_vtbl(proj->mdl), n, v->data);
  assert(m <= n);
  if (m < n) {
    // no subcode for conversion errors
    proj_error(proj, PROJ_ERROR_IN_CONVERT, 0);
    return;
  }

  // build the substitution: evar[i] is mapped to v->data[i]
  tmp = (term_subst_t *) safe_malloc(sizeof(term_subst_t));
  init_term_subst(tmp, proj->mngr, n, proj->evars, v->data);
  proj->val_subst = tmp;
}


/*
 * Delete: free memory
 */
static void proj_delete_avars_to_keep(projector_t *proj) {
  if (proj->avars_to_keep != NULL) {
    delete_int_hset(proj->avars_to_keep);
    safe_free(proj->avars_to_keep);
    proj->avars_to_keep = NULL;
  }
}

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

static void proj_delete_presburger_proj(projector_t *proj) {
  if (proj->presburger != NULL) {
    delete_presburger_projector(proj->presburger);
    safe_free(proj->presburger);
    proj->presburger = NULL;
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
  delete_ivector(&proj->gen_literals);
  delete_ivector(&proj->arith_literals);
  proj_delete_avars_to_keep(proj);
  delete_ivector(&proj->arith_vars);
  delete_ivector(&proj->buffer);

  proj_delete_elim_subst(proj);
  proj_delete_arith_proj(proj);
  proj_delete_val_subst(proj);
  proj_delete_presburger_proj(proj);
}



/*
 * LITERAL ADDITION
 */

/*
 * Process x as an arithmetic variable
 * - if x is not a variable: ignore it and set proj->flag
 * - if x is a variable to eliminate, do nothing
 * - otherwise add x to avars_to_keep and arith_vars if it's not present already
 */
static void proj_add_arith_var(projector_t *proj, term_t x) {
  int_hset_t *avars;
  term_kind_t k;

  assert(is_pos_term(x) && is_arithmetic_term(proj->terms, x));

  k = term_kind(proj->terms, x);
  if (k == UNINTERPRETED_TERM) {
    if (! int_hset_member(&proj->vars_to_elim, x)) {
      avars = proj_get_avars_to_keep(proj);
      if (int_hset_add(avars, x)) {
	ivector_push(&proj->arith_vars, x);
      }
    }
  } else {
    // error: store the term kind for diagnosis
    proj_error(proj, PROJ_ERROR_NON_LINEAR, k);    
  }
}

// collect the variables of p
static void proj_add_poly_vars(projector_t *proj, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;

  if (p->mono[i].var == const_idx) {
    i ++; // skip the constant
  }
  while (i < n) {
    proj_add_arith_var(proj, p->mono[i].var);
    i ++;
  }
}


// either add t or its variables if t is a polynomial
// non-linear terms are not supported here
static void proj_add_arith_term(projector_t *proj, term_t t) {
  term_table_t *terms;

  terms = proj->terms;

  assert(is_arithmetic_term(terms, t));

  switch (term_kind(terms, t)) {
  case ARITH_CONSTANT:
    break;

  case ARITH_POLY:
    proj_add_poly_vars(proj, poly_term_desc(terms, t));
    break;

  default:
    // this will report an error if t isn't a variable
    proj_add_arith_var(proj, t);
    break;
  }  
}


/*
 * Collect all the variables of t then add t to arith_literals
 * - t must be an arithmetic literal
 */
static void proj_add_arith_literal(projector_t *proj, term_t t) {
  term_table_t *terms;
  composite_term_t *eq;

  terms = proj->terms;

  assert(is_arithmetic_literal(terms, t));

  switch (term_kind(terms, t)) {
  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
    proj_add_arith_term(proj, arith_atom_arg(terms, t));
    ivector_push(&proj->arith_literals, t);
    break;

  case ARITH_BINEQ_ATOM:
    eq = arith_bineq_atom_desc(terms, t);
    assert(eq->arity == 2);
    proj_add_arith_term(proj, eq->arg[0]);
    proj_add_arith_term(proj, eq->arg[1]);
    ivector_push(&proj->arith_literals, t);
    break;

  default:
    assert(false);
    break;
  }
  
}


/*
 * Add a literal t
 */
void projector_add_literal(projector_t *proj, term_t t) {
  assert(true_formula(proj, t));

  if (is_arithmetic_literal(proj->terms, t)) {

    //see if we are still on song for cooperdom
    if ( proj->is_presburger && ! is_presburger_literal(proj->terms, t)) {
      proj->is_presburger = false;
    }
    
    /*
     * NOTE: (distinct ...) is not considered an arithmetic literal
     * cf. terms/terms.h so if t is ever a (distinct u1 ... u_n ) it will be
     * processed as a generic literal even if u1 ... u_n are arithmetic
     * terms.
     */
    proj_add_arith_literal(proj, t);
  } else {
    ivector_push(&proj->gen_literals, t);
  }
}


/*
 * GENERIC VARIABLE SUBSTITUTION
 */

/*
 * First pass in model-based projection:
 * - remove variables by substitution
 * - var = variables to eliminate
 * - nvars = size of array vars
 * - input = vector of literals
 */
static void proj_elim_by_substitution(projector_t *proj) {
  elim_subst_t *subst;
  uint32_t i, j, n;
  term_t t, x;

  proj_build_elim_subst(proj);
  subst = proj->elim_subst;

  // Build a substitution: take only the generic literals
  // into account.
  n = proj->gen_literals.size;
  for (i=0; i<n; i++) {
    t = proj->gen_literals.data[i];
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
    n = proj->gen_literals.size;
    j = 0;
    for (i=0; i<n; i++) {
      t = elim_subst_apply(subst, proj->gen_literals.data[i]);
      if (t != true_term) {
	// keep t
	proj->gen_literals.data[j] = t;
	j ++;
      }
    }
    ivector_shrink(&proj->gen_literals, j);
  }

  // Clean-up
  proj_delete_elim_subst(proj);
}



/*
 * ARITHMETIC
 */

/*
 * Add a variable x to the internal arith_projector
 */
static void proj_push_arith_var(projector_t *proj, term_t x, bool to_elim) {
  rational_t *q;
  value_t v;

  assert(proj->arith_proj != NULL);

  v = model_get_term_value(proj->mdl, x);
  q = vtbl_rational(model_get_vtbl(proj->mdl), v);
  aproj_add_var(proj->arith_proj, x, to_elim, q);
}


static void proj_push_presburger_var(projector_t *proj, term_t x, bool to_elim) {
  rational_t *q;
  value_t v;

  assert(proj->presburger != NULL);

  v = model_get_term_value(proj->mdl, x);
  q = vtbl_rational(model_get_vtbl(proj->mdl), v);
  presburger_add_var(proj->presburger, x, to_elim, q);
}


static void proj_process_arith_literals(projector_t *proj) {
  arith_projector_t *aproj;
  term_table_t *terms;
  uint32_t i, j, n;
  term_t x;
  int32_t code;

#if TRACE
  printf("[1]  --> Process arith_literals\n");
  fflush(stdout);
#endif

  proj_build_arith_proj(proj);

  /*
   * Pass all arithmetic variables in proj->evars to the arithmetic projector
   * and remove them from proj->evars.
   */
  terms = proj->terms;
  n = proj->num_evars;
  j = 0;
  for (i=0; i<n; i++) {
    x = proj->evars[i];
    if (is_arithmetic_term(terms, x)) {
      proj_push_arith_var(proj, x, true);
    } else {
      proj->evars[j] = x;
      j ++;
    }
  }
  proj->num_evars = j;

  // Pass all variables from proj->avars to the arith_projector
  n = proj->arith_vars.size;
  for (i=0; i<n; i++) {
    x = proj->arith_vars.data[i];
    assert(is_arithmetic_term(terms, x));
    proj_push_arith_var(proj, x, false);
  }

  // Process the arithmetic literals
  aproj = proj->arith_proj;
  aproj_close_var_set(aproj);
  n = proj->arith_literals.size;
  for (i=0; i<n; i++) {
#if TRACE
    printf("[1]  --> input literal[%"PRIu32"]: (%"PRId32")\n", i, proj->arith_literals.data[i]);
    print_term_full(stdout, terms, proj->arith_literals.data[i]);
    printf("\n");
    fflush(stdout);
#endif
    code = aproj_add_constraint(aproj, proj->arith_literals.data[i]);
    if (code < 0) {
      // Literal not supported by aproj
      proj_error(proj, PROJ_ERROR_BAD_ARITH_LITERAL, code);
      goto done;
    }
  }
  aproj_eliminate(aproj);
  
  // Collect the result in proj->arith_literals
  ivector_reset(&proj->arith_literals);
  aproj_get_formula_vector(aproj, &proj->arith_literals);

#if TRACE
  printf("\n[1]  --> projection result:\n");
  n = proj->arith_literals.size;
  for (i=0; i<n; i++) {
    printf("[1]  --> output literal[%"PRIu32"]: (%"PRId32")\n", i, proj->arith_literals.data[i]);
    print_term_full(stdout, terms, proj->arith_literals.data[i]);
    printf("\n");
  }
  printf("\n\n");
  fflush(stdout);
#endif

 done:
  proj_delete_arith_proj(proj);
}


static void proj_process_presburger_literals(projector_t *proj) {
  presburger_t *pres;
  term_table_t *terms;
  uint32_t i, j, n;
  term_t x;
  int32_t code;

#if TRACE
  printf("[1]  --> Process presburger_literals\n");
  fflush(stdout);
#endif

  proj_build_presburger_proj(proj);

  /*
   * Pass all arithmetic variables in proj->evars to the presburger projector
   * and remove them from proj->evars.
   */
  terms = proj->terms;
  n = proj->num_evars;
  j = 0;
  for (i=0; i<n; i++) {
    x = proj->evars[i];
    if (is_integer_term(terms, x)) {
      proj_push_presburger_var(proj, x, true);
    } else {
      proj->evars[j] = x;
      j ++;
    }
  }
  proj->num_evars = j;

  // Pass all variables from proj->avars to the arith_projector
  n = proj->arith_vars.size;
  for (i=0; i<n; i++) {
    x = proj->arith_vars.data[i];
    assert(is_arithmetic_term(terms, x));
    proj_push_presburger_var(proj, x, false);
  }

  // Process the presburger literals
  pres = proj->presburger;
  presburger_close_var_set(pres);
  n = proj->arith_literals.size;
  for (i=0; i<n; i++) {
#if TRACE
    printf("[1]  --> input literal[%"PRIu32"]: (%"PRId32")\n", i, proj->arith_literals.data[i]);
    print_term_full(stdout, terms, proj->arith_literals.data[i]);
    printf("\n");
    fflush(stdout);
#endif
    code = presburger_add_constraint(pres, proj->arith_literals.data[i]);
    if (code < 0) {
      // Literal not supported by pres
      proj_error(proj, PROJ_ERROR_BAD_PRESBURGER_LITERAL, code);
      goto done;
    }
  }
  presburger_eliminate(pres);
  
  // Collect the result in proj->arith_literals
  ivector_reset(&proj->arith_literals);
  presburger_get_formula_vector(pres, &proj->arith_literals);

#if TRACE
  printf("\n[1]  --> projection result:\n");
  n = proj->arith_literals.size;
  for (i=0; i<n; i++) {
    printf("[1]  --> output literal[%"PRIu32"]: (%"PRId32")\n", i, proj->arith_literals.data[i]);
    print_term_full(stdout, terms, proj->arith_literals.data[i]);
    printf("\n");
  }
  printf("\n\n");
  fflush(stdout);
#endif

 done:
  proj_delete_presburger_proj(proj);
}




/*
 * LAST PHASE
 */

/*
 * Auxiliary function: apply proj->val_subst to all literals of vector v
 * - if there's an error: abort and set proj->flag to ERROR_IN_SUBST
 * - remove all literals that simplify to true by the substitution
 */
static void proj_subst_vector(projector_t *proj, ivector_t *v) {
  term_subst_t *subst;
  uint32_t i, j, n;
  term_t t;
  
  subst = proj->val_subst;
  assert(subst != NULL);

  n = v->size;
  j = 0;
  for (i=0; i<n; i++) {
    t = apply_term_subst(subst, v->data[i]);
    if (t < 0) {
      proj_error(proj, PROJ_ERROR_IN_SUBST, t);
      return;
    }
    if (t != true_term) {
      v->data[j] = t;
      j ++;
    }
  }
  ivector_shrink(v, j);
}

static void proj_elim_by_model_value(projector_t *proj) {
  proj_build_val_subst(proj);
  if (proj->flag == NO_ERROR) {
    proj_subst_vector(proj, &proj->gen_literals);
  }
  if (proj->flag == NO_ERROR) {
    proj_subst_vector(proj, &proj->arith_literals);
  }
  proj_delete_val_subst(proj);
}



/*
 * FULL ELIMINATION
 */

/*
 * Process the literals: eliminate the variables
 * - the result is a  set of literals that don't contain
 *   the variables to eliminate
 * - these literals are added to vector *v
 * - v is not reset
 */
proj_flag_t run_projector(projector_t *proj, ivector_t *v) {
  if (proj->flag == NO_ERROR && proj->gen_literals.size > 0) {
    proj_elim_by_substitution(proj);
  }
  if (proj->flag == NO_ERROR && proj->arith_literals.size > 0) {
    if (proj->is_presburger) {
      proj_process_presburger_literals(proj);
    } else {
      proj_process_arith_literals(proj);
    }
  }

  if (proj->flag == NO_ERROR && proj->num_evars > 0) {  
    // some variables were not eliminated in the first two phases
    // replace them by their value in the model
    proj_elim_by_model_value(proj);
  } 
  
  if (proj->flag == NO_ERROR) {
    /*
     * Copy the results in v
     */
    ivector_add(v, proj->gen_literals.data, proj->gen_literals.size);
    ivector_add(v, proj->arith_literals.data, proj->arith_literals.size);
  }
  
  return proj->flag;
}



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
proj_flag_t project_literals(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t *a,
			     uint32_t nvars, const term_t *var, ivector_t *v) {
  projector_t proj;
  proj_flag_t code;
  uint32_t i;

  init_projector(&proj, mdl, mngr, nvars, var);
  for (i=0; i<n; i++) {
    projector_add_literal(&proj, a[i]);
    if (proj.flag < 0) {
      // record the error code: currently, the only possible error is
      // that literal a[i] is a non-linear arithmetic constraint.
      code = proj.flag;
      goto abort;
    }
  }
  code = run_projector(&proj, v);

 abort:
  delete_projector(&proj);

  return code;
}

 
