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
 * INPUT TO THE EXISTS/FORALL SOLVER
 */

#include <assert.h>
#include <solvers/quant/ef_problem.h>

#include "utils/index_vectors.h"
#include "utils/memalloc.h"

#include "api/search_parameters.h"

#define TRACE 0

#if TRACE
#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif
#include "yices.h"
#endif

/*
 * Delete pattern map
 */
void delete_pattern_map(ptr_hmap_t *m) {
  ptr_hmap_pair_t *p;
  for (p = ptr_hmap_first_record(m);
       p != NULL;
       p = ptr_hmap_next_record(m, p)) {
    ivector_t* list_vector = p->val;
    if (list_vector != NULL) {
      delete_ivector(list_vector);
      safe_free(list_vector);
    }
  }
  delete_ptr_hmap(m);
}

/*
 * Initialization: all empty
 */
void init_ef_prob(ef_prob_t *prob, term_manager_t *mngr, ptr_hmap_t *patterns, ef_param_t *parameters) {
  prob->terms = term_manager_get_terms(mngr);
  prob->manager = mngr;
  prob->all_evars = NULL;
  prob->all_uvars = NULL;
  prob->all_pvars = NULL;
  prob->conditions = NULL;
  prob->num_cnstr = 0;
  prob->cnstr_size = 0;
  prob->cnstr = NULL;
  prob->has_uint = false;

  prob->patterns = NULL;
  prob->parameters = parameters;

  ptr_hmap_t *patterns2;
  ivector_t *pv1;
  ptr_hmap_pair_t *r1, *r2;
  uint32_t n;

  prob->patterns = (ptr_hmap_t *) safe_malloc(sizeof(ptr_hmap_t));

  patterns2 = prob->patterns;
  init_ptr_hmap(patterns2, 0);

  if (patterns != NULL) {
    for (r1 = ptr_hmap_first_record(patterns);
         r1 != NULL;
         r1 = ptr_hmap_next_record(patterns, r1)) {
      pv1 = r1->val;
      n = pv1->size;

      r2 = ptr_hmap_get(patterns2, r1->key);
      if (r2->val == NULL) {
        r2->val = safe_malloc(sizeof(ivector_t));
        init_ivector(r2->val, n);
      }
      ivector_add(r2->val, pv1->data, n);
    }
  }

}


/*
 * Reset to empty
 */
void reset_ef_prob(ef_prob_t *prob) {
  reset_index_vector(prob->all_evars);
  reset_index_vector(prob->all_uvars);
  reset_index_vector(prob->all_pvars);
  reset_index_vector(prob->conditions);
  prob->num_cnstr = 0;
  prob->has_uint = false;

  if (prob->patterns != NULL) {
    delete_pattern_map(prob->patterns);
    safe_free(prob->patterns);
    prob->patterns = NULL;
  }
}


/*
 * Delete
 */
void delete_ef_prob(ef_prob_t *prob) {
  uint32_t i, n;

  delete_index_vector(prob->all_evars);
  delete_index_vector(prob->all_uvars);
  delete_index_vector(prob->all_pvars);
  delete_index_vector(prob->conditions);

  n = prob->num_cnstr;
  for (i=0; i<n; i++) {
    delete_index_vector(prob->cnstr[i].evars);
    delete_index_vector(prob->cnstr[i].uvars);
    delete_index_vector(prob->cnstr[i].pvars);
  }
  safe_free(prob->cnstr);
  prob->cnstr = NULL;
  prob->has_uint = false;

  if (prob->patterns != NULL) {
    delete_pattern_map(prob->patterns);
    safe_free(prob->patterns);
    prob->patterns = NULL;
  }
}


/*
 * Check whether the descriptor is empty:
 */
bool ef_prob_is_empty(ef_prob_t *prob) {
  return iv_is_empty(prob->all_evars) && iv_is_empty(prob->all_uvars)
    && iv_is_empty(prob->conditions) && prob->num_cnstr == 0;
}


/*
 * Make the cnstr array larger
 */
static void extend_ef_prob(ef_prob_t *prob) {
  uint32_t n;

  n = prob->cnstr_size;
  if (n == 0) {
    n = DEF_EF_CNSTR_SIZE;
    assert(n < MAX_EF_CNSTR_SIZE);
    prob->cnstr_size = n;
    prob->cnstr = (ef_cnstr_t *) safe_malloc(n * sizeof(ef_cnstr_t));
  } else {
    n += (n >> 1) + 1; // about 50% larger
    if (n > MAX_EF_CNSTR_SIZE) {
      out_of_memory();
    }
    prob->cnstr_size = n;
    prob->cnstr = (ef_cnstr_t *) safe_realloc(prob->cnstr, n * sizeof(ef_cnstr_t));
  }
}


/*
 * For debugging: check that v is sorted (strictly increasing)
 */
#ifndef NDEBUG
static bool vector_is_sorted(int32_t *v) {
  uint32_t i, n;

  n = iv_len(v);
  for (i=1; i<n; i++) {
    if (v[i-1] >= v[i]) {
      return false;
    }
  }
  return true;
}
#endif


/*
 * Insert x in vector v if it's not already present
 * - v must be sorted
 */
static void insert_elem(int32_t **v, int32_t x) {
  int32_t *u;
  uint32_t i, j, k, n;

  u = *v;

  assert(vector_is_sorted(u));

  i = 0;
  n = iv_len(u);

  j = n;
  while (i < j) {
    // (i + j) can't overflow since n <= MAX_IVECTOR_SIZE < UINT32_MAX/2
    k = (i + j) >> 1;
    assert(i <= k && k < j);
    if (u[k] == x) return;
    if (u[k] < x) {
      i = k+1;
    } else {
      j = k;
    }
  }

  assert(i == j && 0 <= i && i <= n &&
	 (i == n || x < u[i]) &&
	 (i == 0 || u[i-1] < x));


  // make room for one element
  add_index_to_vector(v, 0);
  u = *v;
  assert(iv_size(u) == n+1);

  while (n > i) {
    u[n] = u[n-1];
    n --;
  }
  u[i] = x;

  assert(vector_is_sorted(u));
}


/*
 * Add a[0 ... n-1] to index vector v
 * - v must be sorted
 */
static void add_to_vector(int32_t **v, int32_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    insert_elem(v, a[i]);
  }
}

/*
 * Add v[0...n-1] to all_evars or all_uvars (remove duplicates)
 */
void ef_prob_add_evars(ef_prob_t *prob, term_t *v, uint32_t n) {
  add_to_vector(&prob->all_evars, v, n);
}

void ef_prob_add_uvars(ef_prob_t *prob, term_t *v, uint32_t n) {
  add_to_vector(&prob->all_uvars, v, n);
}

void ef_prob_add_pvars(ef_prob_t *prob, term_t *v, uint32_t n) {
  add_to_vector(&prob->all_pvars, v, n);
}

/*
 * return true if array a has an uninterpreted function/sort
 */
static bool ef_prob_has_uint(ef_prob_t *prob, term_t *a, uint32_t n) {
  term_table_t *terms;
  term_t t;
  uint32_t i;

  terms = prob->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_utype_term(terms, t) || is_function_term(terms, t)) {
      return true;
    }
  }

  return false;
}




/*
 * Add t as a constraint on x
 */
void ef_prob_add_condition(ef_prob_t *prob, term_t t) {
  add_index_to_vector(&prob->conditions, t);
}


/*
 * Add a forall constraint:
 * - ev = existential variables, nev = size of the ev array
 * - uv = universal variables, nuv = size of the uv array
 * - assumption = formula on uv
 * - guarantee = formula on uv and ev
 *
 * The global arrays all_evars and all_uvars are updated:
 * - all_evars := all_evars union ev
 * - all_uvars := all_uvars union uv
 */
void ef_prob_add_constraint(ef_prob_t *prob, term_t *ev, uint32_t nev, term_t *uv, uint32_t nuv,
			    term_t assumption, term_t guarantee, term_t *pv) {
  uint32_t i;
  bool has_uint;

  i = prob->num_cnstr;
  if (i == prob->cnstr_size) {
    extend_ef_prob(prob);
  }
  assert(i < prob->cnstr_size);
  prob->cnstr[i].evars = make_index_vector(ev, nev);
  prob->cnstr[i].uvars = make_index_vector(uv, nuv);
  prob->cnstr[i].pvars = make_index_vector(pv, nuv);
  prob->cnstr[i].assumption = assumption;
  prob->cnstr[i].guarantee = guarantee;
  prob->num_cnstr = i+1;

  has_uint = ef_prob_has_uint(prob, ev, nev);
  if (!has_uint)
    has_uint = ef_prob_has_uint(prob, uv, nuv);
  prob->cnstr[i].has_uint = has_uint;
  if (has_uint)
    prob->has_uint = true;

  ef_prob_add_evars(prob, ev, nev);
  ef_prob_add_uvars(prob, uv, nuv);
  ef_prob_add_pvars(prob, pv, nuv);
}


#if TRACE
/*
 * Print a forall constraint
 */
void ef_print_constraint(FILE *f, ef_cnstr_t *cnstr) {
  uint32_t n;

  fprintf(f, "  constraint:\n");

  n = ef_constraint_num_uvars(cnstr);
  fprintf(f, "    pvars (#%d): ", n);
  yices_pp_term_array(f, n, cnstr->pvars, 120, 1, 0, 1);

  fprintf(f, "    uvars (#%d): ", n);
  yices_pp_term_array(f, n, cnstr->uvars, 120, 1, 0, 1);

  n = ef_constraint_num_evars(cnstr);
  fprintf(f, "    evars (#%d): ", n);
  yices_pp_term_array(f, n, cnstr->evars, 120, 1, 0, 1);

  fprintf(f, "    assumption: ");
  yices_pp_term(f, cnstr->assumption, 120, 1, 0);

  fprintf(f, "    guarantee: ");
  yices_pp_term(f, cnstr->guarantee, 120, 1, 0);

  fprintf(f, "\n");
}

#else
/*
 * Do nothing: but make sure the function is defined
 */
void ef_print_constraint(FILE *f, ef_cnstr_t *cnstr) {
}

#endif

/*
 * Size of vectors
 */
uint32_t ef_prob_num_evars(ef_prob_t *prob) {
  return iv_len(prob->all_evars);
}

uint32_t ef_prob_num_uvars(ef_prob_t *prob) {
  return iv_len(prob->all_uvars);
}

uint32_t ef_prob_num_conditions(ef_prob_t *prob) {
  return iv_len(prob->conditions);
}

uint32_t ef_constraint_num_evars(ef_cnstr_t *cnstr) {
  return iv_len(cnstr->evars);
}

uint32_t ef_constraint_num_uvars(ef_cnstr_t *cnstr) {
  return iv_len(cnstr->uvars);
}


/*
 * Check the type of universal variables
 * - this returns true if some universal variables are integer or real
 */
bool ef_prob_has_arithmetic_uvars(ef_prob_t *prob) {
  term_table_t *terms;
  uint32_t i, n;
  term_t x;

  terms = prob->terms;
  n = iv_len(prob->all_uvars);
  for (i=0; i<n; i++) {
    x = prob->all_uvars[i];
    if (is_arithmetic_term(terms, x)) {
      return true;
    }
  }
  return false;
}


/*
 * Convert prob to an array of formulas (a big conjunction)
 * - all the conditions are added to v
 * - for every constraint, the formula (B_i => C_i) is added to v
 *   (without quantifiers)
 */
void ef_prob_collect_conjuncts(ef_prob_t *prob, ivector_t *v) {
  uint32_t i, n;
  term_t t;

  n = iv_len(prob->conditions);
  for (i=0; i<n; i++) {
    ivector_push(v, prob->conditions[i]);
  }

  n = prob->num_cnstr;
  for (i=0; i<n; i++) {
    t = mk_implies(prob->manager, prob->cnstr[i].assumption, prob->cnstr[i].guarantee);
    ivector_push(v, t);
  }
}


/*
 * Check whether some of the existential variables are skolem functions
 */
bool ef_prob_has_skolem_functions(const ef_prob_t *prob) {
  term_table_t *terms;
  term_t *vars;
  uint32_t i, n;

  terms = prob->terms;
  vars = prob->all_evars;
  n = iv_len(vars);
  for (i=0; i<n; i++) {
    if (is_function_term(terms, vars[i])) {
      return true;
    }
  }

  return false;
}
