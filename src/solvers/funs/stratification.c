/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
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
 * STRATIFICATION: ORGANIZE TYPES/VARIABLES/DISEQUALITIES BY LEVELS
 */

#include "utils/memalloc.h"
#include "solvers/funs/stratification.h"

/*
 * Initialize: use the give type table
 * - allocate a strata array of default size
 */
void init_stratification(stratification_t *s, type_table_t *types) {
  uint32_t n;

  n = DEF_STRATIFICATION_SIZE;
  init_flevel_table(&s->levels, types);
  s->size = n;
  s->nlevels = 0;
  s->nvars = 0;
  s->ndiseqs = 0;
  s->strata = (stratum_t *) safe_malloc(n * sizeof(stratum_t));
  s->vars = NULL;
  s->diseqs = NULL;
}

/*
 * Delete: free memory
 */
void delete_stratification(stratification_t *s) {
  delete_flevel_table(&s->levels);
  safe_free(s->strata);
  safe_free(s->vars);
  safe_free(s->diseqs);
  s->strata = NULL;
  s->vars = NULL;
  s->diseqs = NULL;
}

/*
 * Make the strata array larger
 * - n = minimal size required
 */
static void resize_stratification(stratification_t *s, uint32_t n) {
  uint32_t new_size;

  if (n > MAX_STRATIFICATION_SIZE) {
    out_of_memory();
  }

  // try to double the existing size
  new_size = s->size << 1;
  if (new_size > MAX_STRATIFICATION_SIZE) new_size = MAX_STRATIFICATION_SIZE;
  if (new_size < n) new_size = n;

  assert(new_size >= n && new_size <= MAX_STRATIFICATION_SIZE);
  s->strata = (stratum_t *) safe_realloc(s->strata, new_size * sizeof(stratum_t));
  s->size = new_size;
}

/*
 * Increase the number of levels to n:
 * - make sure s->strata is large enough
 * - initialize s->strata[i] for the i= old nlevels to n-1
 */
static void stratification_increase_num_levels(stratification_t *s, uint32_t n) {
  uint32_t i;

  if (n >= s->size) {
    resize_stratification(s, n);
  }
  assert(n < s->size);

  for (i=s->nlevels; i<n; i++) {
    s->strata[i].nvars = 0;
    s->strata[i].ndiseqs = 0;
    s->strata[i].var_idx = 0;
    s->strata[i].diseq_idx = 0;
  }
  s->nlevels = n;
}


/*
 * FIRST-PASS: determine the size of each stratum.
 */

/*
 * Increment the count of variables of level k = flevel(sigma).
 * - resize array strata if needed.
 */
void stratify_incr_var_count(stratification_t *s, type_t sigma) {
  uint32_t k;

  k = flevel(&s->levels, sigma);
  if (k >= s->nlevels) {
    assert(k < UINT32_MAX); // k+1 won't overflow
    stratification_increase_num_levels(s, k+1);
  }
  assert(k < s->nlevels);
  s->strata[k].nvars ++;
  s->nvars ++;
}

/*
 * Increment the count of disequalities of level k = flevel(sigma)
 */
void stratify_incr_diseq_count(stratification_t *s, type_t sigma) {
  uint32_t k;

  k = flevel(&s->levels, sigma);
  if (k >= s->nlevels) {
    assert(k < UINT32_MAX); // k+1 won't overflow
    stratification_increase_num_levels(s, k+1);
  }
  assert(k < s->nlevels);
  s->strata[k].ndiseqs ++;
  s->ndiseqs ++;
}


/*
 * SECOND PASS: create the variables/disequality arrays.
 */

/*
 * Allocate the arrays for variables and disequalities
 */
void stratify_make_arrays(stratification_t *s) {
  uint32_t i, n;
  uint32_t v, d;

  if (s->nvars > MAX_STRATIFICATION_NUM_VARS ||
      s->ndiseqs > MAX_STRATIFICATION_NUM_DISEQS) {
    /*
     * This should not happen because of limits on
     * the number of egraph terms and disequalities.
     * But just in case, it doesn't hurt to check.
     */
    out_of_memory();
  }

  s->vars = safe_malloc(s->nvars * sizeof(thvar_t));
  s->diseqs = safe_malloc(s->ndiseqs * sizeof(uint32_t));

  // initialize the var_idx/diseq_idx of each stratum
  n = s->nlevels;
  v = 0;
  d = 0;
  for (i=0; i<n; i++) {
    s->strata[i].var_idx = v;
    s->strata[i].diseq_idx = d;
    v += s->strata[i].nvars;
    d += s->strata[i].ndiseqs;
  }
  assert(v == s->nvars);
  assert(d == s->ndiseqs);
}


/*
 * For debugging: end of slice for level k
 */
#ifndef NDEBUG
static uint32_t end_var_slice(const stratification_t *s, uint32_t k) {
  uint32_t i, v;

  v = 0;
  for (i=0; i<=k; i++) {
    v += s->strata[i].nvars;
  }
  return v;
}

static uint32_t end_diseq_slice(const stratification_t *s, uint32_t k) {
  uint32_t i, d;

  d = 0;
  for (i=0; i<=k; i++) {
    d += s->strata[i].ndiseqs;
  }
  return d;
}

#endif

/*
 * Add variable x of type sigma
 */
void stratify_add_var(stratification_t *s, thvar_t x, type_t sigma) {
  uint32_t k, j;

  k = flevel(&s->levels, sigma);
  assert(k < s->nlevels && s->strata[k].var_idx < end_var_slice(s, k));

  j = s->strata[k].var_idx;
  s->vars[j] = x;
  s->strata[k].var_idx ++;
}

/*
 * Add disequality i of type sigma
 */
void stratify_add_diseq(stratification_t *s, uint32_t i, type_t sigma) {
  uint32_t k, j;

  k = flevel(&s->levels, sigma);
  assert(k < s->nlevels && s->strata[k].diseq_idx < end_diseq_slice(s, k));

  j = s->strata[k].diseq_idx;
  s->diseqs[j] = i;
  s->strata[k].diseq_idx ++;  
}


/*
 * Beginning of slices
 * - this should be cheap to compute because the number of levels should be small
 */
uint32_t first_var_in_stratum(const stratification_t *s, uint32_t k) {
  uint32_t i, v;

  assert(k < s->nlevels);

  v = 0;
  for (i=0; i<k; i++) {
    v += s->strata[i].nvars;
  }
  return v;
}

uint32_t first_diseq_in_stratum(const stratification_t *s, uint32_t k) {
  uint32_t i, d;

  assert(k < s->nlevels);

  d = 0;
  for (i=0; i<k; i++) {
    d += s->strata[i].ndiseqs;
  }
  return d;
}
