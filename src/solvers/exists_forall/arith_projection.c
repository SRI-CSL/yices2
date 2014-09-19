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
 * CONSTRAINT DESCRIPTORS
 */

/*
 * Create a new constraint from the content of buffer
 * - buffer must be normalized (and non-zero)
 * - tag = constraint type
 * Side effect: reset buffer
 */
static aproj_constraint_t *make_aproj_constraint(poly_buffer_t *buffer, aproj_tag_t tag) {
  aproj_constraint_t *tmp;
  monomial_t *p;
  uint32_t i, n;

  n = poly_buffer_nterms(buffer);
  assert(n > 0);
  if (n > MAX_APROJ_CONSTRAINT_SIZE) {
    out_of_memory();
  }
  tmp = (aproj_constraint_t *) safe_malloc(sizeof(aproj_constraint_t) + (n+1) * sizeof(monomial_t));
  tmp->tag = tag;
  tmp->nterms = n;

  p = poly_buffer_mono(buffer);
  for (i=0; i<n; i++) {
    tmp->mono[i].var = p[i].var;
    q_init(&tmp->mono[i].coeff);
    q_set(&tmp->mono[i].coeff, &p[i].coeff);
  }
  tmp->mono[i].var = max_idx; // end marker
  reset_poly_buffer(buffer);

  return tmp;
}


/*
 * Delete a constraint descriptor
 */
static void free_aproj_constraint(aproj_constraint_t *c) {
  clear_monarray(c->mono, c->nterms);
  safe_free(c);
}

/*
 * Find the monomial that contains i in c
 * - returns k such that c->mono[k].var == i
 * - returns -1 if i does not occur in c
 */
static int32_t aproj_constraint_find_var(aproj_constraint_t *c, int32_t i) {
  uint32_t l, h, m;

  l = 0;
  h = c->nterms;
  assert(h > 0);

  for (;;) {
    m = (l + h)/2; // can't overflow since c->nterms is smaller than UINT32_MAX/2
    assert(l <= m && m < h && h <= c->nterms);
    if (l == m) break;
    if (c->mono[m].var > i) {
      h = m;
    } else {
      l = m;
    }
  }

  if (c->mono[m].var == i) {
    return m;
  } else {
    return -1;
  }
}



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

  // var index 0 is reserved for the constant idx
  table->term_of[0] = NULL_TERM;
  q_init(table->val + 0);
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
  table->nelims = 1;
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
 * Get the internal index for term x
 * - x must be present in vbtl->tmap
 */
static int32_t aproj_index_of_term(aproj_vtbl_t *vtbl, term_t x) {
  int_hmap_pair_t *d;

  d = int_hmap_find(&vtbl->tmap, x);
  assert(d != NULL && d->val > 0 && d->val < vtbl->nvars);
  return d->val;
}


/*
 * Check whether i is a variable to eliminate
 */
static bool aproj_is_var_to_elim(aproj_vtbl_t *vtbl, int32_t i) {
  assert(i >= 0 && i < max_idx);
  return 0 < i && i < vtbl->nelims;
}


/*
 * Add a constraint to variable i's dependents
 * - i must be a variable to eliminate
 * - update the score of i
 */
static void aproj_add_cnstr_on_var(aproj_vtbl_t *vtbl, int32_t i, aproj_constraint_t *c) {
  int32_t k;

  assert(aproj_is_var_to_elim(vtbl, i));
  assert(aproj_constraint_find_var(c, i) >= 0); // i must occur in c

  ptr_set_add(vtbl->cnstr + i, c); // add c to vtbl->cnstr[i]
  if (c->tag == APROJ_EQ) {
    vtbl->score[i].eq_count ++;
  } else {
    k = aproj_constraint_find_var(c, i);
    if (q_is_pos(&c->mono[k].coeff)) {
      vtbl->score[i].pos_count ++;
    } else {
      vtbl->score[i].neg_count ++;
    }
  }
}


/*
 * Remove c from i's constraints and update the score
 */
static void aproj_remove_cnstr_on_var(aproj_vtbl_t *vtbl, int32_t i, aproj_constraint_t *c) {
  int32_t k;

  assert(aproj_is_var_to_elim(vtbl, i));
  assert(aproj_constraint_find_var(c, i) >= 0); // i must occur in c
  assert(ptr_set_member(vtbl->cnstr[i], c)); // c must occur in constr[i]
	 
  ptr_set_remove(vtbl->cnstr + i, c);
  if (c->tag == APROJ_EQ) {
    assert(vtbl->score[i].eq_count > 0);
    vtbl->score[i].eq_count --;
  } else {
    k = aproj_constraint_find_var(c, i);
    if (q_is_pos(&c->mono[k].coeff)) {
      assert(vtbl->score[i].pos_count > 0);
      vtbl->score[i].pos_count --;
    } else {
      assert(vtbl->score[i].neg_count > 0);
      vtbl->score[i].neg_count --;
    }
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
 * Delete all constraint descriptors in proj
 */
static void cnstr_free_iterator(void *aux, void *p) {  
  free_aproj_constraint(p);
}

static void free_constraints(arith_projector_t *proj) {
  ptr_set_iterate(proj->constraints, NULL, cnstr_free_iterator);
}

/*
 * Reset:
 * - remove all variables and constraints
 * - reset all internal tables.
 */
void reset_arith_projector(arith_projector_t *proj) {
  reset_aproj_vtbl(&proj->vtbl);
  free_constraints(proj);
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
  free_constraints(proj);
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
 * Add/remove a descriptor to/from a projector structure
 * - update the dependencies and scores
 */
static void aproj_add_cnstr(arith_projector_t *proj, aproj_constraint_t *c) {
  aproj_vtbl_t *vtbl;
  uint32_t i, n;
  int32_t x;

  ptr_set_add(&proj->constraints, c);

  vtbl = &proj->vtbl;
  n = c->nterms;
  for (i=0; i<n; i++) {
    x = c->mono[i].var;
    if (aproj_is_var_to_elim(vtbl, x)) {
      aproj_add_cnstr_on_var(vtbl, x, c);
    }
  }
}

// c must be present in proj->constraint
static void aproj_remove_cnstr(arith_projector_t *proj, aproj_constraint_t *c) {
  aproj_vtbl_t *vtbl;
  uint32_t i, n;
  int32_t x;

  ptr_set_remove(&proj->constraints, c);

  vtbl = &proj->vtbl;
  n = c->nterms;
  for (i=0; i<n; i++) {
    x = c->mono[i].var;
    if (aproj_is_var_to_elim(vtbl, x)) {
      aproj_remove_cnstr_on_var(vtbl, x, c);
    }
  }
}


/*
 * Build linear polynomials in buffer
 * - replace the term id by the correspodnding internal variable
 */
static void aproj_buffer_add_var(poly_buffer_t *buffer, aproj_vtbl_t *vtbl, term_t t) {
  int32_t i;

  i = aproj_index_of_term(vtbl, t);
  poly_buffer_add_var(buffer, i);
}

static void aproj_buffer_sub_var(poly_buffer_t *buffer, aproj_vtbl_t *vtbl, term_t t) {
  int32_t i;

  i = aproj_index_of_term(vtbl, t);
  poly_buffer_sub_var(buffer, i);
}

static void aproj_buffer_add_mono(poly_buffer_t *buffer, aproj_vtbl_t *vtbl, term_t t, rational_t *a) {
  int32_t i;

  i = aproj_index_of_term(vtbl, t);
  poly_buffer_add_monomial(buffer, i, a);
}

static void aproj_buffer_sub_mono(poly_buffer_t *buffer, aproj_vtbl_t *vtbl, term_t t, rational_t *a) {
  int32_t i;

  i = aproj_index_of_term(vtbl, t);
  poly_buffer_sub_monomial(buffer, i, a);
}

static void aproj_buffer_add_poly(poly_buffer_t *buffer, aproj_vtbl_t *vtbl, polynomial_t *p) {
  uint32_t i, n;
  term_t x;

  n = p->nterms;

  if (n > 0) {
    i = 0;
    // deal with the constant if any
    if (p->mono[0].var == const_idx) {
      poly_buffer_add_const(buffer, &p->mono[0].coeff);
      i ++;
    }
    while (i < n) {
      x = p->mono[i].var;
      aproj_buffer_add_mono(buffer, vtbl, x, &p->mono[i].coeff);
      i ++;
    }
  }
}

static void aproj_buffer_sub_poly(poly_buffer_t *buffer, aproj_vtbl_t *vtbl, polynomial_t *p) {
  uint32_t i, n;
  term_t x;

  n = p->nterms;

  if (n > 0) {
    i = 0;
    // deal with the constant if any
    if (p->mono[0].var == const_idx) {
      poly_buffer_sub_const(buffer, &p->mono[0].coeff);
      i ++;
    }
    while (i < n) {
      x = p->mono[i].var;
      aproj_buffer_sub_mono(buffer, vtbl, x, &p->mono[i].coeff);
      i ++;
    }
  }
}


/*
 * Normalize buffer then build a constraint from its content and add the
 * constraint.
 * - tag = the constraint type.
 */
static void add_constraint_from_buffer(arith_projector_t *proj, poly_buffer_t *buffer, aproj_tag_t tag) {
  aproj_constraint_t *c;

  normalize_poly_buffer(buffer);
  c = make_aproj_constraint(buffer, tag);
  aproj_add_cnstr(proj, c);  
}


/*
 * Build and add a constraint
 * - convert term ids to internal variables
 */
// constraint t == 0
static void aproj_add_var_eq_zero(arith_projector_t *proj, term_t t) {
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_add_var(buffer, &proj->vtbl, t);
  add_constraint_from_buffer(proj, buffer, APROJ_EQ);
}

// constraint t >= 0
static void aproj_add_var_geq_zero(arith_projector_t *proj, term_t t) {
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_add_var(buffer, &proj->vtbl, t);
  add_constraint_from_buffer(proj, buffer, APROJ_GE);
}

// constraint t < 0 (converted to -t > 0)
static void aproj_add_var_lt_zero(arith_projector_t *proj, term_t t) {
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_sub_var(buffer, &proj->vtbl, t);
  add_constraint_from_buffer(proj, buffer, APROJ_GT);
}

// constraint p == 0
static void aproj_add_poly_eq_zero(arith_projector_t *proj, polynomial_t *p) {
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_add_poly(buffer, &proj->vtbl, p);
  add_constraint_from_buffer(proj, buffer, APROJ_EQ);
}

// constraint p >= 0
static void aproj_add_poly_geq_zero(arith_projector_t *proj, polynomial_t *p) {
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_add_poly(buffer, &proj->vtbl, p);
  add_constraint_from_buffer(proj, buffer, APROJ_GE);
}

// constraint p < 0 (converted to -p > 0)
static void aproj_add_poly_lt_zero(arith_projector_t *proj, polynomial_t *p) {
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  aproj_buffer_sub_poly(buffer, &proj->vtbl, p);
  add_constraint_from_buffer(proj, buffer, APROJ_GT);
}


// constraint (eq t1 t2)
static void aproj_add_arith_bineq(arith_projector_t *proj, composite_term_t *eq) {
  poly_buffer_t *buffer;
  term_table_t *terms;
  term_t t1, t2;

  assert(eq->arity == 2);
  t1 = eq->arg[0];
  t2 = eq->arg[1];

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  terms = proj->terms;
  switch (term_kind(terms, t1)) {
  case ARITH_CONSTANT:    
    poly_buffer_add_const(buffer, rational_term_desc(terms, t1));
    break;

  case ARITH_POLY:
    aproj_buffer_add_poly(buffer, &proj->vtbl, poly_term_desc(terms, t1));
    break;

  default:
    aproj_buffer_add_var(buffer, &proj->vtbl, t1);
    break;
  }

  switch (term_kind(terms, t2)) {
  case ARITH_CONSTANT:    
    poly_buffer_sub_const(buffer, rational_term_desc(terms, t2));
    break;

  case ARITH_POLY:
    aproj_buffer_sub_poly(buffer, &proj->vtbl, poly_term_desc(terms, t2));
    break;

  default:
    aproj_buffer_sub_var(buffer, &proj->vtbl, t2);
    break;
  }
  add_constraint_from_buffer(proj, buffer, APROJ_EQ);
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
  term_table_t *terms;
  term_t t;

  assert(good_term(proj->terms, c) && is_boolean_term(proj->terms, c));

  if (proj->constraints == NULL) {
    close_aproj_vtbl(&proj->vtbl);
  }

  terms = proj->terms;
  switch (term_kind(terms, c)) {
  case CONSTANT_TERM:
    assert(c == true_term);
    break;

  case ARITH_EQ_ATOM:
    assert(is_pos_term(c)); // no negation allowed
    t = arith_eq_arg(terms, c);
    if (term_kind(terms, t) == ARITH_POLY) {
      aproj_add_poly_eq_zero(proj, poly_term_desc(terms, t));
    } else {
      aproj_add_var_eq_zero(proj, t);
    }
    break;

  case ARITH_BINEQ_ATOM:
    assert(is_pos_term(c)); // no negation allowed
    aproj_add_arith_bineq(proj, arith_bineq_atom_desc(terms, c));
    break;

  case ARITH_GE_ATOM:
    t = arith_ge_arg(terms, c);    
    if (is_pos_term(c)) {
      // atom (t >= 0)
      if (term_kind(terms, t) == ARITH_POLY) {
	aproj_add_poly_geq_zero(proj, poly_term_desc(terms, t));
      } else {
	aproj_add_var_geq_zero(proj, t);
      }
    } else {
      // atom (t < 0)
      if (term_kind(terms, t) == ARITH_POLY) {
	aproj_add_poly_lt_zero(proj, poly_term_desc(terms, t));
      } else {
	aproj_add_var_lt_zero(proj, t);
      }
    }
    break;

  default:
    assert(false);
    break;
  }
}

