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
  table->nelims = 1;
  table->size = n;
  table->esize = m;

  table->term_of = (term_t *) safe_malloc(n * sizeof(term_t));
  table->val = (rational_t *) safe_malloc(n * sizeof(rational_t));

  table->cnstr = (ptr_set_t **) safe_malloc(m * sizeof(ptr_set_t *));
  table->score = (aproj_score_t *) safe_malloc(m * sizeof(aproj_score_t));

  // var index 0 is reserved: the constant idx
  table->term_of[0] = NULL_TERM;
  q_set_one(table->val + 0);
  table->cnstr[0] = NULL;
  table->score[0].eq_count = 0;
  table->score[0].pos_count = 0;
  table->score[0].neg_count = 0;

  init_int_hmap(&table->tmap, 0);
}


/*
 * Increase the size of arrays term_of and val
 */
static void increase_aproj_vtbl_size(aproj_vtbl_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1; // about 50% larger
  if (n > MAX_APROJ_VTBL_SIZE) {
    out_of_memory();
  }
  table->size = n;
  table->term_of = (term_t *) safe_realloc(table->term_of, n * sizeof(term_t));
  table->val = (rational_t *) safe_realloc(table->val, n * sizeof(rational_t));
}

/*
 * Increase the size of arrays cnstr and score
 */
static void increase_aproj_vtbl_esize(aproj_vtbl_t *table) {
  uint32_t n;

  n = table->esize + 1;
  n += n>>1;
  if (n > table->size) {
    n = table->size;
  }
  table->esize = n;
  table->cnstr = (ptr_set_t **) safe_realloc(table->cnstr, n * sizeof(ptr_set_t *));
  table->score = (aproj_score_t *) safe_realloc(table->score, n * sizeof(aproj_score_t));
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
 * Add a new variable x to table
 * - q = value for x
 * - to_elim: if true, x is added as a variable to eliminate
 *   otherwise, x is added as a variable to keep.
 * - since we don't know all variables yet, we don't add the
 *   mapping from idx --> x in table->tmap.
 */
static void aproj_vtbl_add_var(aproj_vtbl_t *table, term_t x, bool to_elim, rational_t *q) {
  uint32_t i, j;

  // make room for a new variable
  i = table->nvars;
  if (i == table->size) {
    increase_aproj_vtbl_size(table);
  }
  assert(i < table->size);
  table->nvars = i+1;
  q_init(table->val + i);
  
  if (to_elim) {
    j = table->nelims;
    if (j == table->esize) {
      increase_aproj_vtbl_esize(table);
    }
    assert(j < table->esize);
    table->nelims = j+1;
    table->cnstr[j] = NULL;
    table->score[j].eq_count = 0;
    table->score[j].pos_count = 0;
    table->score[j].neg_count = 0;

    /*
     * We store x as var[j] where j = table->nelims.
     * If var[j] is already used, we move it to var[i]
     */
    assert(j <= i);
    if (j < i) {
      table->term_of[i] = table->term_of[j];
      q_set(table->val + i, table->val + j);
      i = j; // to store x in term_of[i] and set q
    }
  }

  table->term_of[i] = x;
  q_set(table->val + i, q);
}


/*
 * Complete table: after all variables have been added.
 * - all variables in [1 ... nelims - 1] are to be eliminated
 * - all variables in [nelems .. nvars - 1] are to be kept
 * - for all variable i, we add the mapping term_of[i] --> i
 *   in table->tmap
 */
static void close_aproj_vtbl(aproj_vtbl_t *vtbl) {
  int_hmap_pair_t *d;
  uint32_t i, n;
  term_t x;

  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    x = vtbl->term_of[i];
    d = int_hmap_get(&vtbl->tmap, x);
    assert(d->val < 0);
    d->val = i;
  }
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
  init_poly_buffer(&proj->buffer);
  q_init(&proj->q1);
  q_init(&proj->q2);
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
  reset_poly_buffer(&proj->buffer);
  q_clear(&proj->q1);
  q_clear(&proj->q2);
}


/*
 * Delete: free memory
 */
void delete_arith_projector(arith_projector_t *proj) {
  delete_aproj_vtbl(&proj->vtbl);
  free_ptr_set(proj->constraints);
  proj->constraints = NULL;
  delete_poly_buffer(&proj->buffer);
  q_clear(&proj->q1);
  q_clear(&proj->q2);
}


/*
 * Add variable x
 * - x must be a valid term index in proj->terms
 * - x must be distinct from all previously added variables
 * - if to_elim is true then x is a marked as a variable to 
 *   eliminate, otherwise x is a variable to keep
 * - q = value of x in the model
 * - proj must not have any constraints: all variables must be
 *   declared before the first call to aproj_add_constraint 
 */
void aproj_add_var(arith_projector_t *proj, term_t x, bool to_elim, rational_t *q) {
  assert(good_term(proj->terms, x) && proj->constraints == NULL);
  aproj_vtbl_add_var(&proj->vtbl, x, to_elim, q);
}


/*
 * Add constraint c
 * - c must be an arithmetic predicate of the following forms
 *    (ARITH_EQ_ATOM t)
 *    (ARITH_BINEQ_ATOM t1 t2)
 *    (ARITH_GE_ATOM t)
 *    (NOT (ARITH_GE_ATOM t))
 *   where t, t1, t2 are either variables declared in proj or linear
 *   polynomials in variables declared in proj
 * - c must be true in the model specified by calls to aproj_add_var
 * - no variables can be added after this function is called
 */
void aproj_add_constraint(arith_projector_t *proj, term_t c) {
  assert(good_term(proj->terms, c));

  if (proj->constraints == NULL) {
    close_aproj_vtbl(&proj->vtbl);
  }
}

