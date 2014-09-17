/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * MODEL-BASED QUANTIFIER ELIMINATION FOR LINEAR ARITHMETIC
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "solvers/exists_forall/arith_projection.h"


/*
 * VARIABLE TABLE
 */

/*
 * Initialize table:
 * - n = initial size of arrays term_of and val
 * - m = initial isze of arrays cnstr and score
 * If n is 0, them default sizes are used.
 * If n is positive and m is 0, then the default esize is used unless it's 
 * larger than n. If the default is more than n, then the initial esize is 
 * set to n.
 */
static void init_aproj_vtbl(aproj_vtbl_t *table, uint32_t n, uint32_t m) {
  assert(m <= n);

  if (n == 0) {
    n = DEF_APROJ_VTBL_SIZE;
    m = DEF_APROJ_VTBL_ESIZE;
  } else if (m == 0) {
    m = DEF_APROJ_VTBL_ESIZE;
    if (n < m) {
      m = n;
    }
  }

  if (n > MAX_APROJ_VTBL_SIZE) {
    out_of_memory();
  }

  table->nvars = 1;
  table->nelims = 0;
  table->size = n;
  table->esize = m;

  table->term_of = (term_t *) safe_malloc(n * sizeof(term_t));
  table->val = (rational_t *) safe_malloc(n * sizeof(rational_t));

  table->cnstr = (ptr_set_t **) safe_malloc(m * sizeof(ptr_set_t *));
  table->score = (aproj_score_t *) safe_malloc(m * sizeof(aproj_score_t));

  // var index 0 is reserved: the constant idx
  table->term_of[0] = NULL_TERM;
  q_set_one(table->val + 0);
  
  init_int_hmap(&table->tmap, 0);
}



/*
 * Empty table
 */
static void reset_aproj_vtbl(aproj_vtbl_t *table) {
  uint32_t i, n;

  assert(table->nvars >= 1);

  // free the rationals except val[0]
  n = table->nvars;
  for (i=1; i<n; i++) {
    q_clear(table->val + i);
  }

  n = table->nelims;
  for (i=0; i<n; i++) {
    free_ptr_set(table->cnstr[i]);
  }

  int_hmap_reset(&table->tmap);

  table->nvars = 1;
  table->nelims = 0;
}


/*
 * Delete
 */
static void delete_aproj_vtbl(aproj_vtbl_t *table) {
  uint32_t i, n;
  
  n = table->nvars;
  for (i=0; i<n; i++) {
    q_clear(table->val + i);
  }
  n = table->nelims;
  for (i=0; i<n; i++) {
    free_ptr_set(table->cnstr[i]);
  }
  delete_int_hmap(&table->tmap);

  safe_free(table->term_of);
  safe_free(table->val);
  safe_free(table->cnstr);
  safe_free(table->score);

  table->term_of = NULL;
  table->val = NULL;
  table->cnstr = NULL;
  table->score = NULL;
}







/*
 * PROJECTOR
 */

/*
 * Initialize proj
 * - mngr = relevant term manager
 * - n = initial size (total number of variables)
 * - m = initial esize (number of variables to eliminate)
 * - m must be no more than m
 *
 * Parameters n and m specify the initial size and esize
 * - if n is 0, the default size and esize are used (m should be 0 too)
 * - if n>0 and m=0, the initial size is n and the initial esize is
 *   min(n, default esize).
 */
void init_arith_projector(arith_projector_t *proj, term_manager_t *mngr, uint32_t n, uint32_t m) {
  proj->terms = term_manager_get_terms(mngr);
  proj->manager = mngr;
  init_aproj_vtbl(&proj->vtbl, n, m);
  proj->constraints = NULL;
}


/*
 * Reset:
 * - remove all variables and constraints
 * - reset all internal tables.
 */
void reset_arith_projector(arith_projector_t *proj) {
  reset_aproj_vtbl(&proj->vtbl);
  free_ptr_set(proj->constraints);
  proj->constraints = NULL;
}


/*
 * Delete: free memory
 */
void delete_arith_projector(arith_projector_t *proj) {
  delete_aproj_vtbl(&proj->vtbl);
  free_ptr_set(proj->constraints);
  proj->constraints = NULL;
}


