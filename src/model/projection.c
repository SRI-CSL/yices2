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


#ifdef HAVE_MCSAT
#include "mcsat/na/na_plugin_explain.h"
#endif


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

  proj->is_nonlinear = false;
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
 * Build val_subst for the selected variables var[0 ... n-1].
 * This is used before arithmetic projection to substitute integer
 * eliminands without also substituting real eliminands.
 */
static void proj_build_selected_val_subst(projector_t *proj, uint32_t n, const term_t *var) {
  term_subst_t *tmp;
  ivector_t *v;
  uint32_t m;
  int32_t code;

  assert(proj->val_subst == NULL);
  assert(n > 0);

  v = &proj->buffer;
  resize_ivector(v, n);

  code = evaluate_term_array(proj->mdl, n, var, v->data);
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

  // build the substitution: var[i] is mapped to v->data[i]
  tmp = (term_subst_t *) safe_malloc(sizeof(term_subst_t));
  init_term_subst(tmp, proj->mngr, n, var, v->data);
  proj->val_subst = tmp;
}


static bool term_array_contains(uint32_t n, const term_t *a, term_t x) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] == x) {
      return true;
    }
  }
  return false;
}


static bool ivector_contains_term(const ivector_t *v, term_t x) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    if (v->data[i] == x) {
      return true;
    }
  }
  return false;
}


static void ivector_push_term_once(ivector_t *v, term_t x) {
  if (!ivector_contains_term(v, x)) {
    ivector_push(v, x);
  }
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
 * - if x is a variable to eliminate, do nothing
 * - otherwise add x to avars_to_keep and arith_vars if it's not present already
 */
static void proj_add_arith_var(projector_t *proj, term_t x) {
  int_hset_t *avars;

  assert(is_pos_term(x) && is_arithmetic_term(proj->terms, x) &&
	 term_kind(proj->terms, x) == UNINTERPRETED_TERM);

  if (! int_hset_member(&proj->vars_to_elim, x)) {
    avars = proj_get_avars_to_keep(proj);
    if (int_hset_add(avars, x)) {
      ivector_push(&proj->arith_vars, x);
    }
  }
}

static void proj_add_arith_term(projector_t *proj, term_t t);

// collect the variables of p
static void proj_add_poly_vars(projector_t *proj, polynomial_t *p) {
  uint32_t i, n;
  term_t var;

  n = p->nterms;
  i = 0;

  if (p->mono[i].var == const_idx) {
    i ++; // skip the constant
  }
  while (i < n) {
    var = p->mono[i].var;
    proj_add_arith_term(proj, var);
    i ++;
  }
}

// collect the variables of p
static void proj_add_pprod_vars(projector_t *proj, pprod_t *p) {
#ifdef HAVE_MCSAT
  uint32_t i, n;
  term_t var;

  proj->is_nonlinear = true;
  proj->is_presburger = false;

  n = p->len;
  i = 0;

  while (i < n) {
    var = p->prod[i].var;
    proj_add_arith_term(proj, var);
    i ++;
  }
#else
  proj_error(proj, PROJ_ERROR_NON_LINEAR, POWER_PRODUCT);
  return;
#endif
}


// either add t or its variables if t is a polynomial or a power product
static void proj_add_arith_term(projector_t *proj, term_t t) {
  term_table_t *terms;
  term_kind_t k;

  terms = proj->terms;

  assert(is_arithmetic_term(terms, t));

  k = term_kind(terms, t);
  switch (k) {
  case UNINTERPRETED_TERM:
    proj_add_arith_var(proj, t);
    break;

  case ARITH_CONSTANT:
    break;

  case ARITH_POLY:
    proj_add_poly_vars(proj, poly_term_desc(terms, t));
    break;

  case POWER_PRODUCT:
    proj_add_pprod_vars(proj, pprod_term_desc(terms, t));
    break;

  default:
    // not supported
    proj_error(proj, PROJ_ERROR_UNSUPPORTED_ARITH_TERM, k);
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

static void proj_subst_vector(projector_t *proj, ivector_t *v);
static void proj_elim_by_model_value(projector_t *proj);
static void proj_process_presburger_literals(projector_t *proj);

/*
 * Check whether any real arithmetic variable still needs arithmetic
 * projection.
 */
static bool proj_has_real_evar(projector_t *proj) {
  term_table_t *terms;
  uint32_t i, n;

  terms = proj->terms;
  n = proj->num_evars;
  for (i=0; i<n; i++) {
    if (is_real_term(terms, proj->evars[i])) {
      return true;
    }
  }
  return false;
}


static bool proj_has_integer_evar(projector_t *proj) {
  term_table_t *terms;
  uint32_t i, n;

  terms = proj->terms;
  n = proj->num_evars;
  for (i=0; i<n; i++) {
    if (is_integer_term(terms, proj->evars[i])) {
      return true;
    }
  }
  return false;
}


/*
 * Substitute var[0 ... nvars-1] by their model values.
 * The substituted variables are also removed from proj->evars.
 */
static void proj_subst_evar_array(projector_t *proj, uint32_t nvars, const term_t *var) {
  term_t x;
  uint32_t i, j, n;

  if (nvars == 0) {
    return;
  }

  proj_build_selected_val_subst(proj, nvars, var);

  if (proj->flag == PROJ_NO_ERROR) {
    proj_subst_vector(proj, &proj->gen_literals);
  }
  if (proj->flag == PROJ_NO_ERROR) {
    proj_subst_vector(proj, &proj->arith_literals);
  }
  proj_delete_val_subst(proj);

  if (proj->flag != PROJ_NO_ERROR) {
    return;
  }

  n = proj->num_evars;
  j = 0;
  for (i=0; i<n; i++) {
    x = proj->evars[i];
    if (!term_array_contains(nvars, var, x)) {
      proj->evars[j] = x;
      j ++;
    }
  }
  proj->num_evars = j;
}


static void proj_collect_evars_by_type(projector_t *proj, ivector_t *v, bool integers) {
  term_table_t *terms;
  term_t x;
  uint32_t i, n;

  terms = proj->terms;
  n = proj->num_evars;
  for (i=0; i<n; i++) {
    x = proj->evars[i];
    if (integers ? is_integer_term(terms, x) : is_real_term(terms, x)) {
      ivector_push(v, x);
    }
  }
}


/*
 * Substitute integer eliminands by their model values before using the
 * real-arithmetic projection machinery.
 */
static void proj_subst_integer_evars(projector_t *proj) {
  ivector_t int_evars;

  init_ivector(&int_evars, 0);
  proj_collect_evars_by_type(proj, &int_evars, true);
  proj_subst_evar_array(proj, int_evars.size, int_evars.data);
  delete_ivector(&int_evars);
}


static void proj_init_route_copy(projector_t *dst, projector_t *src) {
  init_projector(dst, src->mdl, src->mngr, src->num_evars, src->evars);
  ivector_copy(&dst->gen_literals, src->gen_literals.data, src->gen_literals.size);
  ivector_copy(&dst->arith_literals, src->arith_literals.data, src->arith_literals.size);
  ivector_copy(&dst->arith_vars, src->arith_vars.data, src->arith_vars.size);
  dst->is_presburger = src->is_presburger;
  dst->is_nonlinear = src->is_nonlinear;
}


static void proj_reset_arith_var_collection(projector_t *proj) {
  proj_delete_avars_to_keep(proj);
  ivector_reset(&proj->arith_vars);
}


/*
 * Reclassify the current arithmetic literals structurally.
 *
 * This intentionally reuses proj_add_arith_literal/proj_add_arith_term rather
 * than relying on is_presburger_literal alone: the latter is a shallow
 * integer-type test and does not reject residual power products.
 */
static void proj_reclassify_arith_literals(projector_t *proj) {
  ivector_t lits;
  uint32_t i, n;
  term_t t;

  init_ivector(&lits, proj->arith_literals.size);
  ivector_copy(&lits, proj->arith_literals.data, proj->arith_literals.size);
  ivector_reset(&proj->arith_literals);
  proj_reset_arith_var_collection(proj);
  proj->is_presburger = true;
  proj->is_nonlinear = false;

  n = lits.size;
  for (i=0; i<n; i++) {
    t = lits.data[i];
    if (t == true_term) {
      continue;
    }
    if (t == false_term) {
      proj_error(proj, PROJ_ERROR_IN_SUBST, t);
      break;
    }
    if (is_arithmetic_literal(proj->terms, t)) {
      if (proj->is_presburger && !is_presburger_literal(proj->terms, t)) {
        proj->is_presburger = false;
      }
      proj_add_arith_literal(proj, t);
    } else {
      ivector_push(&proj->gen_literals, t);
    }
    if (proj->flag != PROJ_NO_ERROR) {
      break;
    }
  }

  delete_ivector(&lits);
}


static bool proj_evar_member(projector_t *proj, term_t x) {
  uint32_t i, n;

  n = proj->num_evars;
  for (i=0; i<n; i++) {
    if (proj->evars[i] == x) {
      return true;
    }
  }
  return false;
}


static void proj_collect_pprod_int_evars_in_term(projector_t *proj, term_t t, ivector_t *v);

static void proj_collect_pprod_int_evars_in_poly(projector_t *proj, polynomial_t *p, ivector_t *v) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (i < n && p->mono[i].var == const_idx) {
    i ++;
  }
  while (i < n) {
    proj_collect_pprod_int_evars_in_term(proj, p->mono[i].var, v);
    i ++;
  }
}


static void proj_collect_pprod_int_evars_in_pprod(projector_t *proj, pprod_t *p, ivector_t *v) {
  term_table_t *terms;
  uint32_t i, n;
  term_t x;

  terms = proj->terms;
  n = p->len;
  for (i=0; i<n; i++) {
    x = p->prod[i].var;
    if (is_integer_term(terms, x) && proj_evar_member(proj, x)) {
      ivector_push_term_once(v, x);
    }
    proj_collect_pprod_int_evars_in_term(proj, x, v);
  }
}


static void proj_collect_pprod_int_evars_in_term(projector_t *proj, term_t t, ivector_t *v) {
  switch (term_kind(proj->terms, t)) {
  case ARITH_POLY:
    proj_collect_pprod_int_evars_in_poly(proj, poly_term_desc(proj->terms, t), v);
    break;

  case POWER_PRODUCT:
    proj_collect_pprod_int_evars_in_pprod(proj, pprod_term_desc(proj->terms, t), v);
    break;

  default:
    break;
  }
}


static void proj_collect_pprod_int_evars(projector_t *proj, ivector_t *v) {
  composite_term_t *eq;
  uint32_t i, n;
  term_t t;

  n = proj->arith_literals.size;
  for (i=0; i<n; i++) {
    t = proj->arith_literals.data[i];
    switch (term_kind(proj->terms, t)) {
    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
      proj_collect_pprod_int_evars_in_term(proj, arith_atom_arg(proj->terms, t), v);
      break;

    case ARITH_BINEQ_ATOM:
      eq = arith_bineq_atom_desc(proj->terms, t);
      assert(eq->arity == 2);
      proj_collect_pprod_int_evars_in_term(proj, eq->arg[0], v);
      proj_collect_pprod_int_evars_in_term(proj, eq->arg[1], v);
      break;

    default:
      break;
    }
  }
}


static term_t proj_choose_integer_evar(projector_t *proj, ivector_t *priority) {
  term_table_t *terms;
  uint32_t i, n;
  term_t x;

  terms = proj->terms;
  n = priority->size;
  for (i=0; i<n; i++) {
    x = priority->data[i];
    if (proj_evar_member(proj, x) && is_integer_term(terms, x)) {
      return x;
    }
  }

  n = proj->num_evars;
  for (i=0; i<n; i++) {
    x = proj->evars[i];
    if (is_integer_term(terms, x)) {
      return x;
    }
  }

  return NULL_TERM;
}


static bool proj_route_result(projector_t *route, ivector_t *result) {
  if (route->flag == PROJ_NO_ERROR && route->num_evars > 0) {
    proj_elim_by_model_value(route);
  }
  if (route->flag != PROJ_NO_ERROR) {
    return false;
  }
  ivector_add(result, route->gen_literals.data, route->gen_literals.size);
  ivector_add(result, route->arith_literals.data, route->arith_literals.size);
  return true;
}


static bool proj_run_presburger_salvage(projector_t *proj, ivector_t *result) {
  ivector_t real_evars, priority;
  term_t x;

  init_ivector(&real_evars, 0);
  proj_collect_evars_by_type(proj, &real_evars, false);
  proj_subst_evar_array(proj, real_evars.size, real_evars.data);
  delete_ivector(&real_evars);
  if (proj->flag != PROJ_NO_ERROR) {
    return false;
  }

  proj_reclassify_arith_literals(proj);
  if (proj->flag != PROJ_NO_ERROR) {
    return false;
  }

  init_ivector(&priority, 0);
  proj_collect_pprod_int_evars(proj, &priority);
  while (!proj->is_presburger && proj_has_integer_evar(proj)) {
    x = proj_choose_integer_evar(proj, &priority);
    if (x == NULL_TERM) {
      break;
    }
    proj_subst_evar_array(proj, 1, &x);
    if (proj->flag != PROJ_NO_ERROR) {
      delete_ivector(&priority);
      return false;
    }
    proj_reclassify_arith_literals(proj);
    if (proj->flag != PROJ_NO_ERROR) {
      delete_ivector(&priority);
      return false;
    }
  }
  delete_ivector(&priority);

  if (proj->is_presburger && proj->arith_literals.size > 0 && proj_has_integer_evar(proj)) {
    proj_process_presburger_literals(proj);
    if (proj->flag != PROJ_NO_ERROR) {
      return false;
    }
  }

  return proj_route_result(proj, result);
}


static void proj_commit_route_result(projector_t *proj, ivector_t *result) {
  ivector_reset(&proj->gen_literals);
  ivector_reset(&proj->arith_literals);
  ivector_add(&proj->arith_literals, result->data, result->size);
  proj->num_evars = 0;
}


static bool proj_make_route_term(projector_t *proj, ivector_t *result, term_t *out) {
  if (result->size == 0) {
    *out = true_term;
    return true;
  }
  *out = mk_and_safe(proj->mngr, result->size, result->data);
  return *out != NULL_TERM;
}


static void proj_factor_common_route_terms(ivector_t *left, ivector_t *right,
                                           ivector_t *common, ivector_t *left_only, ivector_t *right_only) {
  uint32_t i, n;
  term_t t;

  n = left->size;
  for (i=0; i<n; i++) {
    t = left->data[i];
    if (ivector_contains_term(right, t)) {
      ivector_push_term_once(common, t);
    } else {
      ivector_push(left_only, t);
    }
  }

  n = right->size;
  for (i=0; i<n; i++) {
    t = right->data[i];
    if (!ivector_contains_term(common, t)) {
      ivector_push(right_only, t);
    }
  }
}


static void proj_commit_route_or(projector_t *proj, ivector_t *left, ivector_t *right) {
  ivector_t common, left_only, right_only;
  term_t route_terms[2];
  term_t t;

  init_ivector(&common, 0);
  init_ivector(&left_only, 0);
  init_ivector(&right_only, 0);
  proj_factor_common_route_terms(left, right, &common, &left_only, &right_only);

  if (!proj_make_route_term(proj, &left_only, &route_terms[0]) ||
      !proj_make_route_term(proj, &right_only, &route_terms[1])) {
    proj_error(proj, PROJ_ERROR_IN_SUBST, 0);
    goto done;
  }

  t = mk_or_safe(proj->mngr, 2, route_terms);
  if (t == NULL_TERM) {
    proj_error(proj, PROJ_ERROR_IN_SUBST, 0);
    goto done;
  }

  ivector_reset(&proj->gen_literals);
  ivector_reset(&proj->arith_literals);
  ivector_add(&proj->arith_literals, common.data, common.size);
  if (t != true_term) {
    ivector_push(&proj->arith_literals, t);
  }
  proj->num_evars = 0;

 done:
  delete_ivector(&common);
  delete_ivector(&left_only);
  delete_ivector(&right_only);
}

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


static void proj_process_real_arith_literals(projector_t *proj) {
  arith_projector_t *aproj;
  term_table_t *terms;
  uint32_t i, j, n;
  term_t x;
  int32_t code;

#if TRACE
  printf("[1]  --> Process arith_literals\n");
  fflush(stdout);
#endif

  proj_subst_integer_evars(proj);
  if (proj->flag != PROJ_NO_ERROR) {
    return;
  }
  if (proj->arith_literals.size == 0) {
    return;
  }
  if (! proj_has_real_evar(proj)) {
    return;
  }

#ifdef HAVE_MCSAT
  // check if there are any variables assigned to an algebraic number in the model
  // TODO: is this necessary, linear projection shouldn't rely on rationals
  for (i = 0; !proj->is_nonlinear && i < proj->num_evars; ++ i) {
    x = proj->evars[i];
    value_t v = model_get_term_value(proj->mdl, x);
    if (object_is_algebraic(&proj->mdl->vtbl, v)) {
      proj->is_nonlinear = true;
    }
  }
  for (i = 0; !proj->is_nonlinear && i < proj->arith_vars.size; ++ i) {
    x = proj->arith_vars.data[i];
    value_t v = model_get_term_value(proj->mdl, x);
    if (object_is_algebraic(&proj->mdl->vtbl, v)) {
      proj->is_nonlinear = true;
    }
  }
  if (proj->is_nonlinear) {
    // project
    code = na_project_arith_literals(&proj->arith_literals, proj->mdl, proj->mngr,
				      proj->num_evars, proj->evars,
				      proj->arith_vars.size, proj->arith_vars.data);
    if (code < 0) {
      proj_error(proj, PROJ_ERROR_NON_LINEAR, code);
      return;
    }
    // remove the arithmetic variables from the elimination list
    terms = proj->terms;
    n = proj->num_evars;
    j = 0;
    for (i=0; i<n; i++) {
      x = proj->evars[i];
      if (!is_arithmetic_term(terms, x)) {
        proj->evars[j] = x;
        j ++;
      }
    }
    proj->num_evars = j;
    return;
  }
#endif

  assert(!proj->is_nonlinear);

  proj_build_arith_proj(proj);

  /*
   * Pass all real arithmetic variables in proj->evars to the arithmetic
   * projector and remove them from proj->evars.
   */
  terms = proj->terms;
  n = proj->num_evars;
  j = 0;
  for (i=0; i<n; i++) {
    x = proj->evars[i];
    if (is_real_term(terms, x)) {
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


static void proj_process_arith_literals(projector_t *proj) {
  projector_t pres_route, real_route;
  ivector_t int_evars, real_evars, pres_result, real_result;
  bool have_ints, have_reals, pres_ok, real_ok;

  init_ivector(&int_evars, 0);
  init_ivector(&real_evars, 0);
  proj_collect_evars_by_type(proj, &int_evars, true);
  proj_collect_evars_by_type(proj, &real_evars, false);
  have_ints = int_evars.size > 0;
  have_reals = real_evars.size > 0;
  delete_ivector(&int_evars);
  delete_ivector(&real_evars);

  if (!have_ints) {
    proj_process_real_arith_literals(proj);
    return;
  }

  if (!have_reals) {
    init_ivector(&pres_result, 0);
    proj_init_route_copy(&pres_route, proj);
    pres_ok = proj_run_presburger_salvage(&pres_route, &pres_result);
    delete_projector(&pres_route);
    if (pres_ok) {
      proj_commit_route_result(proj, &pres_result);
      delete_ivector(&pres_result);
      return;
    }
    delete_ivector(&pres_result);

    proj_process_real_arith_literals(proj);
    return;
  }

  init_ivector(&pres_result, 0);
  init_ivector(&real_result, 0);

  proj_init_route_copy(&pres_route, proj);
  pres_ok = proj_run_presburger_salvage(&pres_route, &pres_result);
  delete_projector(&pres_route);

  proj_init_route_copy(&real_route, proj);
  proj_process_real_arith_literals(&real_route);
  real_ok = proj_route_result(&real_route, &real_result);
  delete_projector(&real_route);

  if (pres_ok && real_ok) {
    proj_commit_route_or(proj, &pres_result, &real_result);
  } else if (pres_ok) {
    proj_commit_route_result(proj, &pres_result);
  } else if (real_ok) {
    proj_commit_route_result(proj, &real_result);
  } else {
    proj_process_real_arith_literals(proj);
  }

  delete_ivector(&pres_result);
  delete_ivector(&real_result);
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
  if (proj->flag == YICES_NO_ERROR) {
    proj_subst_vector(proj, &proj->gen_literals);
  }
  if (proj->flag == YICES_NO_ERROR) {
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
  if (proj->flag == YICES_NO_ERROR && proj->gen_literals.size > 0) {
    proj_elim_by_substitution(proj);
  }
  if (proj->flag == YICES_NO_ERROR && proj->arith_literals.size > 0) {
    if (proj->is_presburger) {
      proj_process_presburger_literals(proj);
    } else {
      proj_process_arith_literals(proj);
    }
  }

  if (proj->flag == YICES_NO_ERROR && proj->num_evars > 0) {  
    // some variables were not eliminated in the first two phases
    // replace them by their value in the model
    proj_elim_by_model_value(proj);
  } 
  
  if (proj->flag == YICES_NO_ERROR) {
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
 * - extra_error = to store more error information.
 *
 * The terms in a[0 ... n-1] must all be arithmetic/bitvectors
 * or Boolean literals. (A Boolean literal is either (= p q) or
 * (not (= p q)) or p or (not p), where p and q are Boolean terms).
 *
 * Return code: PROJ_NO_ERROR if everything worked or a negative
 * error code otherwise.

 * If the return code is PROJ_ERROR_UNSUPPORTED_ARITH_TERM then
 * *extra_error contains the term_kind of the invalid term encountered.
 *
 * Otherwise, extra_error is unchanged.
 * Return code: 0 means no error
 */
proj_flag_t project_literals(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t *a,
			     uint32_t nvars, const term_t *var, ivector_t *v, int32_t *extra_error) {
  projector_t proj;
  proj_flag_t code;
  uint32_t i;

  init_projector(&proj, mdl, mngr, nvars, var);
  for (i=0; i<n; i++) {
    projector_add_literal(&proj, a[i]);
    if (proj.flag < 0) {
      // unsupported term or non-linear arithmetic
      code = proj.flag;
      *extra_error = proj.error_code;
      goto abort;
    }
  }
  code = run_projector(&proj, v);

 abort:
  delete_projector(&proj);

  return code;
}

 
