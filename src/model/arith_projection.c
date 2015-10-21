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

#include "model/arith_projection.h"
#include "terms/rba_buffer_terms.h"
#include "utils/memalloc.h"
#include "utils/ptr_array_sort2.h"
#include "utils/ptr_vectors.h"

#define TRACE 0

#if TRACE
#include <inttypes.h>
#include "io/term_printer.h"
#endif


/*
 * CONSTRAINT DESCRIPTORS
 */
#if TRACE
static void print_aproj_monomial(FILE *f, rational_t *coeff, int32_t x, bool first) {
  bool negative;
  bool abs_one;

  negative = q_is_neg(coeff);
  if (negative) {
    if (first) {
      fprintf(f, "-");
      if (x != const_idx) {
        fprintf(f, " ");
      }
    } else {
      fprintf(f, " - ");
    }
    abs_one = q_is_minus_one(coeff);
  } else {
    if (! first) {
      fprintf(f, " + ");
    }
    abs_one = q_is_one(coeff);
  }

  if (x == const_idx) {
    q_print_abs(f, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(f, coeff);
      fprintf(f, "*");
    }
    fprintf(f, "x!%"PRId32, x);
  }
}

static void print_aproj_constraint(FILE *f, aproj_constraint_t *c) {
  uint32_t i, n;
  bool first;

  fprintf(f, "constraint[%"PRIu32"]: (", c->id);
  n = c->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_aproj_monomial(f, &c->mono[i].coeff, c->mono[i].var, first);
      first = false;
    }
  }

  switch (c->tag) {
  case APROJ_GT:
    fputs(" > 0)", f);
    break;
  case APROJ_GE:
    fputs(" >= 0)", f);
    break;
  case APROJ_EQ:
    fputs(" = 0)", f);
    break;
  }
}
#endif

/*
 * Create a new constraint from the content of buffer
 * - buffer must be normalized (and non-zero)
 * - tag = constraint type
 * - id = identifier
 * Side effect: reset buffer
 */
static aproj_constraint_t *make_aproj_constraint(poly_buffer_t *buffer, aproj_tag_t tag, uint32_t id) {
  aproj_constraint_t *tmp;
  monomial_t *p;
  uint32_t i, n;

  n = poly_buffer_nterms(buffer);
  assert(n > 0);
  if (n > MAX_APROJ_CONSTRAINT_SIZE) {
    out_of_memory();
  }
  tmp = (aproj_constraint_t *) safe_malloc(sizeof(aproj_constraint_t) + (n+1) * sizeof(monomial_t));
  tmp->id = id;
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
 * Divide c by rational q
 */
static void divide_aproj_constraint(aproj_constraint_t *c, rational_t *q) {
  uint32_t i, n;

  assert(q_is_nonzero(q));

  n = c->nterms;
  for (i=0; i<n; i++) {
    q_div(&c->mono[i].coeff, q);
  }
}


/*
 * Negate the coefficients
 */
static void negate_aproj_constraint(aproj_constraint_t *c) {
  in_place_negate_monarray(c->mono);
}



/*
 * For debugging: check that i has coefficient +1 or -1 in c
 */
#ifndef NDEBUG
static bool aproj_var_coeff_is_one(aproj_constraint_t *c, int32_t i) {
  int32_t k;

  k = aproj_constraint_find_var(c, i);
  return k >= 0 && q_is_one(&c->mono[k].coeff);
}

static bool aproj_var_coeff_is_minus_one(aproj_constraint_t *c, int32_t i) {
  int32_t k;

  k = aproj_constraint_find_var(c, i);
  return k >= 0 && q_is_minus_one(&c->mono[k].coeff);
}
#endif


/*
 * HASH FUNCTION
 */

/*
 * Hash function to interface with ptr_set2
 * - aux is ignored,
 * - p is a constraint descriptor
 */
static uint32_t jenkins_hash_constraint(void *aux, void *p) {
  uint32_t x;

  x = ((aproj_constraint_t *) p)->id;

  x = (x + 0x7ed55d16) + (x<<12);
  x = (x ^ 0xc761c23c) ^ (x>>19);
  x = (x + 0x165667b1) + (x<<5);
  x = (x + 0xd3a2646c) ^ (x<<9);
  x = (x + 0xfd7046c5) + (x<<3);
  x = (x ^ 0xb55a4f09) ^ (x>>16);

  return x;
}

/*
 * Descriptor for the hash function
 */
static const ptr_set2_hash_t hash_desc = {
  jenkins_hash_constraint, NULL
};


/*
 * VARIABLE TABLE
 */

/*
 * Comparison function for the heap: return true if x is cheaper to eliminate
 * than y (heuristic based on scores).
 * - the first argument in the variable table
 */
static bool aproj_cheaper_var(void *table, int32_t x, int32_t y);

/*
 * Initialize table:
 * - n = initial size of arrays term_of and val
 * - m = initial size of arrays cnstr and score
 * If n is 0, then default sizes are used.
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

  table->cnstr = (ptr_set2_t **) safe_malloc(m * sizeof(ptr_set2_t *));
  table->score = (aproj_score_t *) safe_malloc(m * sizeof(aproj_score_t));

  // var index 0 is reserved for the constant idx
  table->term_of[0] = NULL_TERM;
  q_init(table->val + 0);
  q_set_one(table->val + 0);
  table->cnstr[0] = NULL;
  table->score[0].eq_count = 0;
  table->score[0].pos_count = 0;
  table->score[0].neg_count = 0;

  init_generic_heap(&table->heap, 0, 0, aproj_cheaper_var, table);

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
  table->cnstr = (ptr_set2_t **) safe_realloc(table->cnstr, n * sizeof(ptr_set2_t *));
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
    free_ptr_set2(table->cnstr[i]);
  }

  reset_generic_heap(&table->heap);
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
    free_ptr_set2(table->cnstr[i]);
  }
  delete_generic_heap(&table->heap);
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
 * - all variables in [nelims .. nvars - 1] are to be kept
 * - for all variable i, we add the mapping term_of[i] --> i
 *   in table->tmap
 * - then we add all variables to eliminate to the heap
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

  n = vtbl->nelims;
  for (i=1; i<n; i++) {
    generic_heap_add(&vtbl->heap, i);
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
 * Term that variable i represents
 */
static inline term_t aproj_term_of_var(aproj_vtbl_t *vtbl, int32_t i) {
  assert(1 <= i && i < vtbl->nvars);
  return vtbl->term_of[i];
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

  ptr_set2_add(vtbl->cnstr + i, &hash_desc, c); // add c to vtbl->cnstr[i]
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

  if (generic_heap_member(&vtbl->heap, i)) {
    generic_heap_update(&vtbl->heap, i);
  }
}


/*
 * Remove c from i's constraints and update the score
 */
static void aproj_remove_cnstr_on_var(aproj_vtbl_t *vtbl, int32_t i, aproj_constraint_t *c) {
  int32_t k;

  assert(aproj_is_var_to_elim(vtbl, i));
  assert(aproj_constraint_find_var(c, i) >= 0); // i must occur in c
  assert(ptr_set2_member(vtbl->cnstr[i], &hash_desc, c)); // c must occur in cnstr[i]
	 
  ptr_set2_remove(vtbl->cnstr + i, &hash_desc, c);
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

  if (generic_heap_member(&vtbl->heap, i)) {
    generic_heap_update(&vtbl->heap, i);
  }
}



/*
 * Cleanup after elimination of variable i
 * - reset cnstr[i] to NULL 
 * - reset all counters
 */
static void aproj_cleanup_var_data(aproj_vtbl_t *vtbl, int32_t i) {
  assert(aproj_is_var_to_elim(vtbl, i));

  vtbl->cnstr[i] = NULL;
  vtbl->score[i].eq_count = 0;
  vtbl->score[i].pos_count = 0;
  vtbl->score[i].neg_count = 0;
}


/*
 * Get value of x in the model:
 * - x can be const_idx here
 */
static inline rational_t *aproj_var_val(aproj_vtbl_t *vtbl, int32_t x) {
  assert(0 <= x && x < vtbl->nvars && q_is_one(vtbl->val + 0));
  return vtbl->val + x;
}

/*
 * Evaluate c->mono in the model
 * - store the result in val
 */
static void aproj_eval_cnstr_in_model(aproj_vtbl_t *vtbl, rational_t *val, aproj_constraint_t *c) {
  uint32_t i, n;
  int32_t x;

  q_clear(val);
  n = c->nterms;
  for (i=0; i<n; i++) {
    x = c->mono[i].var;
    q_addmul(val, &c->mono[i].coeff, aproj_var_val(vtbl, x));
  }  
}

#ifndef NDEBUG
/*
 * Check whether c is true in the model
 */
static bool aproj_good_constraint(arith_projector_t *proj, aproj_constraint_t *c) {
  rational_t aux;
  bool result;

  result = false;

  q_init(&aux);
  aproj_eval_cnstr_in_model(&proj->vtbl, &aux, c);
  switch (c->tag) {
  case APROJ_GE:
    result = q_is_nonneg(&aux);
    break;
  case APROJ_GT:
    result = q_is_pos(&aux);
    break;
  case APROJ_EQ:
    result = q_is_zero(&aux);
    break;
  }
  q_clear(&aux);

  return result;
}

#endif



/*
 * ORDERING ON VARIABLES
 */

/*
 * We order variables based on the scores data structures. Variables that
 * are cheap to eliminate occur first in the ordering.
 *
 * Trivial variables: if the score of x is one of the following then
 * we can just remove all constraints on x and we're done.
 * - eq_count = 1, pos_count = 0, neg_count = 0
 * - eq_count = 0, pos_count = anything, neg_count = 0
 * - eq_count = 0, pos_count = 0, neg_count = anything
 *
 * After trivial variables, we put all x that occur in one or more equality
 * - we can eliminate x by substitution
 *
 * Then: cheap cases of Fourier-Motzkin elimination:
 * - eq_count = 0, pos_count = 1, neg_count = anything
 * - eq_count = 0, pos_count = anything, neg_count = 1
 * - eq_count = 0, pos_count = 2, neg_count = 2
 *
 * Then the other variables: sorted by pos_count + neg_count
 */
typedef enum {
  APROJ_TRIVIAL,
  APROJ_SUBST,
  APROJ_CHEAP,
  APROJ_EXPENSIVE,
} var_group_t;

/*
 * Group of a variable x that has a score of the form [0, px, nx]
 */
static const var_group_t group_tbl[4][4] = {
  { APROJ_TRIVIAL, APROJ_TRIVIAL, APROJ_TRIVIAL,   APROJ_TRIVIAL },   // px = 0
  { APROJ_TRIVIAL, APROJ_CHEAP,   APROJ_CHEAP,     APROJ_CHEAP },     // px = 1
  { APROJ_TRIVIAL, APROJ_CHEAP,   APROJ_CHEAP,     APROJ_EXPENSIVE }, // px = 2
  { APROJ_TRIVIAL, APROJ_CHEAP,   APROJ_EXPENSIVE, APROJ_EXPENSIVE }, // px >= 3
};

static var_group_t aproj_var_group(aproj_vtbl_t *vtbl, int32_t x) {
  aproj_score_t *score;
  var_group_t group;
  uint32_t px, nx;

  assert(aproj_is_var_to_elim(vtbl, x));
  score = vtbl->score + x;  

  switch (score->eq_count) {
  case 0:
    /*
     * px in {0, 1, 2, 3} = min(3, pos_count of x)
     * nx in {0, 1, 2, 3} = min(3, neg_count of x)
     */
    px = score->pos_count;
    if (px > 3) px = 3;
    nx = score->neg_count;
    if (nx > 3) nx = 3;
    group = group_tbl[px][nx];
    break;

  case 1:
    group = APROJ_SUBST;
    if (score->pos_count == 0 && score->neg_count == 0) {
      group = APROJ_TRIVIAL;
    }
    break;

  default:
    group = APROJ_SUBST;
    break;
  }

  return group;
}


/*
 * Secondary metrics: if x and y are in the same group,
 * we count the total number of constraints on x and y to break ties.
 */
static uint32_t aproj_all_count(aproj_vtbl_t *vtbl, int32_t x) {
  aproj_score_t *score;

  assert(aproj_is_var_to_elim(vtbl, x));
  score = vtbl->score + x;
  return score->eq_count + score->pos_count + score->neg_count;
}


/*
 * Comparison function:
 * - x and y are two variables to eliminate
 * - table is a variable table
 * - return true if x is cheaper to eliminate than y
 */
static bool aproj_cheaper_var(void *table, int32_t x, int32_t y) {
  aproj_vtbl_t *vtbl;
  var_group_t gx, gy;

  vtbl = table;
  gx = aproj_var_group(vtbl, x);
  gy = aproj_var_group(vtbl, y);

  return (gx < gy) || (gx == gy && aproj_all_count(vtbl, x) < aproj_all_count(vtbl, y));
}





/*
 * PROJECTOR
 */

/*
 * Initialize proj
 * - mngr = relevant term manager
 * - n = initial size (total number of variables)
 * - m = initial esize (number of variables to eliminate)
 * - n must be no more than m
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
  proj->next_id = 0;
  init_poly_buffer(&proj->buffer);
  init_poly_buffer(&proj->buffer2);
  q_init(&proj->q1);
  q_init(&proj->q2);
  init_pvector(&proj->pos_vector, 10);
  init_pvector(&proj->neg_vector, 10);
}


/*
 * Delete all constraint descriptors in proj
 */
static void cnstr_free_iterator(void *aux, void *p) {  
  free_aproj_constraint(p);
}

static void free_constraints(arith_projector_t *proj) {
  ptr_set2_iterate(proj->constraints, NULL, cnstr_free_iterator);
}

/*
 * Reset:
 * - remove all variables and constraints
 * - reset all internal tables.
 */
void reset_arith_projector(arith_projector_t *proj) {
  reset_aproj_vtbl(&proj->vtbl);
  free_constraints(proj);
  free_ptr_set2(proj->constraints);
  proj->constraints = NULL;
  reset_poly_buffer(&proj->buffer);
  reset_poly_buffer(&proj->buffer2);
  q_clear(&proj->q1);
  q_clear(&proj->q2);
  pvector_reset(&proj->pos_vector);
  pvector_reset(&proj->neg_vector);
}


/*
 * Delete: free memory
 */
void delete_arith_projector(arith_projector_t *proj) {
  delete_aproj_vtbl(&proj->vtbl);
  free_constraints(proj);
  free_ptr_set2(proj->constraints);
  proj->constraints = NULL;
  delete_poly_buffer(&proj->buffer);
  delete_poly_buffer(&proj->buffer2);
  q_clear(&proj->q1);
  q_clear(&proj->q2);
  delete_pvector(&proj->pos_vector);
  delete_pvector(&proj->neg_vector);
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
 * Close the set of variables and prepare for addition of constraints.
 * - this function must be called once all variables have been added
 *   and before adding the first constraint.
 
 */
void aproj_close_var_set(arith_projector_t *proj) {
  close_aproj_vtbl(&proj->vtbl);
}



/*
 * Add/remove a descriptor to/from a projector structure
 * - update the dependencies and scores
 */
static void aproj_add_cnstr(arith_projector_t *proj, aproj_constraint_t *c) {
  aproj_vtbl_t *vtbl;
  uint32_t i, n;
  int32_t x;

  ptr_set2_add(&proj->constraints, &hash_desc, c);

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

  ptr_set2_remove(&proj->constraints, &hash_desc, c);

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
 * - replace the term id by the corresponding internal variable
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
 * For debugging: check that the constraint defined by buffer/tag
 * is trivially true.
 */
#ifndef NDEBUG
static bool trivial_constraint_in_buffer(poly_buffer_t *buffer, aproj_tag_t tag) {
  bool r;

  assert(poly_buffer_is_constant(buffer));
  r = false;
  switch (tag) {
  case APROJ_GT:
    r = poly_buffer_is_pos_constant(buffer);
    break;
  case APROJ_GE:
    r = poly_buffer_is_nonneg_constant(buffer);
    break;
  case APROJ_EQ:
    r = poly_buffer_is_zero(buffer);
    break;
  }

  return r;
}

#endif

/*
 * Normalize buffer then build a constraint from its content and add the
 * constraint.
 * - tag = the constraint type.
 */
static void add_constraint_from_buffer(arith_projector_t *proj, poly_buffer_t *buffer, aproj_tag_t tag) {
  aproj_constraint_t *c;

  normalize_poly_buffer(buffer);
  if (poly_buffer_is_constant(buffer)) {
    // trivial constraint
    assert(trivial_constraint_in_buffer(buffer, tag));
    reset_poly_buffer(buffer);
  } else {
    c = make_aproj_constraint(buffer, tag, proj->next_id);
    assert(aproj_good_constraint(proj, c));
    aproj_add_cnstr(proj, c);
#if TRACE
    printf("--> adding constraint\n");
    print_aproj_constraint(stdout, c);
    printf("\n");
    fflush(stdout);
#endif
    proj->next_id ++;
  }
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
 *
 * Return code:
 * - 0 means that c was accepted and added to the set of constraints
 * - a negative code means that c is rejected:
 *   - NOT_ARITH_LITERAL means that c is not an arithmetic literal
 *   - ARITH_DISEQ means that c is either (NOT (ARITH_EQ_ATOM t))
 *                 or (NOT (ARITH_BINEQ_ATOM t1 t2))
 *   - FALSE_ATOM means that c is 'false_term'.
 *
 */
int32_t aproj_add_constraint(arith_projector_t *proj, term_t c) {
  term_table_t *terms;
  term_t t;
  int32_t code;

  assert(good_term(proj->terms, c) && is_boolean_term(proj->terms, c));

  code = 0;
  terms = proj->terms;
  switch (term_kind(terms, c)) {
  case CONSTANT_TERM:
    /*
     * c is either true_term or false_term
     * for true_term, we do nothing
     * for false_term we return an error code.
     */
    if (c == false_term) {
      code = APROJ_ERROR_FALSE_LITERAL;
    }
    break;

  case ARITH_EQ_ATOM:
    if (is_neg_term(c)) {
      code = APROJ_ERROR_ARITH_DISEQ;
    } else {
      t = arith_eq_arg(terms, c);
      if (term_kind(terms, t) == ARITH_POLY) {
	aproj_add_poly_eq_zero(proj, poly_term_desc(terms, t));
      } else {
	aproj_add_var_eq_zero(proj, t);
      }
    }
    break;

  case ARITH_BINEQ_ATOM:
    if (is_neg_term(c)) {
      code = APROJ_ERROR_ARITH_DISEQ;
    } else {
      aproj_add_arith_bineq(proj, arith_bineq_atom_desc(terms, c));
    }
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
    code = APROJ_ERROR_NOT_ARITH_LITERAL;
    break;
  }

  return code;
}



/*
 * SUPPORT FOR VARIABLE ELIMINATION
 */

/*
 * Remove c from proj->constraints and from cnstr[x] for all x/=y
 */
static void aproj_remove_cnstr_var(arith_projector_t *proj, aproj_constraint_t *c, int32_t y) {
  aproj_vtbl_t *vtbl;
  uint32_t i, n;
  int32_t x;

  ptr_set2_remove(&proj->constraints, &hash_desc, c);

  vtbl = &proj->vtbl;
  n = c->nterms;
  for (i=0; i<n; i++) {
    x = c->mono[i].var;
    if (x != y && aproj_is_var_to_elim(vtbl, x)) {
      aproj_remove_cnstr_on_var(vtbl, x, c);
    }
  }
}


/*
 * Detach all the constraints that depend on i:
 * - i must not be trivial (so it must have constraints attached)
 * - remove them from the global constraint set and from the dependency sets
 *   of all variables, except i.
 */
static void aproj_detach_all_constraints_on_var(arith_projector_t *proj, int32_t i) {
  ptr_set2_t *set;
  aproj_constraint_t *c;
  uint32_t k, n;

  assert(aproj_is_var_to_elim(&proj->vtbl, i));

  set = proj->vtbl.cnstr[i];
  assert(set != NULL);

  n = set->size;
  for (k=0; k<n; k++) {
    c = set->data[k];
    if (live_ptr_elem(c)) {
      aproj_remove_cnstr_var(proj, c, i);
    }
  }
}



/*
 * ELIMINATION OF TRIVIAL VARIABLES
 */
static void aproj_remove_all_constraints_on_var(arith_projector_t *proj, int32_t i) {
  ptr_set2_t *set;
  aproj_constraint_t *c;
  uint32_t k, n;

  assert(aproj_is_var_to_elim(&proj->vtbl, i));

  set = proj->vtbl.cnstr[i];
  if (set != NULL) {
    n = set->size;
    for (k=0; k<n; k++) {
      c = set->data[k];
      if (live_ptr_elem(c)) {
	aproj_remove_cnstr_var(proj, c, i);
	free_aproj_constraint(c);
      }
    }

    free_ptr_set2(set);
    aproj_cleanup_var_data(&proj->vtbl, i);
  }
}



/*
 * ELIMINATION BY SUBSTITUTION
 */

/*
 * Make the coefficient of i equal to 1 in c
 * - i must occur in c
 * - c should be an equality
 */
static void aproj_normalize_eq(arith_projector_t *proj, aproj_constraint_t *c, int32_t i) {
  int32_t k;

  k = aproj_constraint_find_var(c, i);
  assert(k >= 0);
  if (q_is_minus_one(&c->mono[k].coeff)) {
    negate_aproj_constraint(c);
  } else if (! q_is_one(&c->mono[k].coeff)) {
    q_set(&proj->q1, &c->mono[k].coeff);
    divide_aproj_constraint(c, &proj->q1);
  }

  assert(aproj_var_coeff_is_one(c, i));
}


/*
 * Apply substitution defined by eq to constraint c
 * - i = variable to eliminate
 * - the coeff of i in eq must be equal to 1
 * - this creates a new constraint d that does not contain i, 
 *   and d is added to proj
 */
static void aproj_subst_constraint(arith_projector_t *proj, aproj_constraint_t *c, aproj_constraint_t *eq, int32_t i) {  
  poly_buffer_t *buffer;
  rational_t *a;
  int32_t k;

  assert(aproj_var_coeff_is_one(eq, i));

  // a := coefficient of i in c
  k = aproj_constraint_find_var(c, i);
  assert(k >= 0);
  a = &proj->q1;
  q_set(a, &c->mono[k].coeff);

  // build c - a * eq in buffer
  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  poly_buffer_add_monarray(buffer, c->mono, c->nterms);
  poly_buffer_submul_monarray(buffer, eq->mono, eq->nterms, a);

  // add new constraint: same tag as c
  add_constraint_from_buffer(proj, buffer, c->tag);  
}


/*
 * Apply substitution defined by eq to all constraints that contain i,
 * then remove all constraints on i.
 * - i = variable to eliminate
 * - i must have coefficient 1 in eq
 * - eq must not occur in proj->vtbl.cnstr[i]
 */
static void aproj_substitute_eq(arith_projector_t *proj, aproj_constraint_t *eq, int32_t i) {
  ptr_set2_t *set;
  aproj_constraint_t *c;
  uint32_t k, n;

  set = proj->vtbl.cnstr[i];
  assert(set != NULL);

  n = set->size;
  for (k=0; k<n; k++) {
    c = set->data[k];
    if (live_ptr_elem(c)) {
      assert(c != eq);
      aproj_subst_constraint(proj, c, eq, i);
      free_aproj_constraint(c);
    }
  }

  // clean up: delete the set and reset the counters
  free_ptr_set2(set);
  aproj_cleanup_var_data(&proj->vtbl, i);
}


/*
 * Select an equality constraint that contains variable i
 * - i must have positive eq_count
 * - return an equality with the smallest number of terms
 *   the returned constraint is removed form i's set and from proj->constraint)
 */
static aproj_constraint_t *aproj_pick_eq(arith_projector_t *proj, int32_t i) {
  ptr_set2_t *set;
  aproj_constraint_t *c, *d;
  uint32_t k, n, size;

  assert(aproj_is_var_to_elim(&proj->vtbl, i) && proj->vtbl.score[i].eq_count > 0);

  c = NULL;
  size = UINT32_MAX; // this is larger than MAX_APROJ_CONSTRAINT_SIZE

  set = proj->vtbl.cnstr[i];
  assert(set != NULL);
  
  n = set->size;
  for (k=0; k<n; k++) {
    d = set->data[k];
    if (live_ptr_elem(d) && d->tag == APROJ_EQ && d->nterms < size) {
      c = d;
      size = d->nterms;
    }
  }

  assert(c != NULL);
  aproj_remove_cnstr(proj, c);

  return c;
}


/*
 * Eliminate variable i by substitution
 * - i must have positive eq_count
 */
static void aproj_elim_var_subst(arith_projector_t *proj, int32_t i) {
  aproj_constraint_t *eq;

  eq = aproj_pick_eq(proj, i);
  aproj_normalize_eq(proj, eq, i);

  aproj_detach_all_constraints_on_var(proj, i);
  aproj_substitute_eq(proj, eq, i);
  free_aproj_constraint(eq);
}



/*
 * ELIMINATION USING FOURIER-MOTZKIN OR VIRTUAL TERM SUBSTITUTION
 */

/*
 * Normalize inequality c involving i then move it either to
 * pos_vector or to neg_vector.
 * - let a be the coefficient of i in c
 * - if a is positive, then  1/a * c is added to pos_vector
 * - if a is negative, then -1/a * c is added to neg_vector
 */
static void aproj_normalize_inequality(arith_projector_t *proj, aproj_constraint_t *c, int32_t i) {
  int32_t k;

  k = aproj_constraint_find_var(c, i);
  assert(k >= 0);

  if (q_is_pos(&c->mono[k].coeff)) {
    if (! q_is_one(&c->mono[k].coeff)) {
      q_set(&proj->q1, &c->mono[k].coeff);
      divide_aproj_constraint(c, &proj->q1);
    }
    assert(aproj_var_coeff_is_one(c, i));
    assert(aproj_good_constraint(proj, c));

    pvector_push(&proj->pos_vector, c);

  } else {
    assert(q_is_neg(&c->mono[k].coeff));
    
    if (! q_is_minus_one(&c->mono[k].coeff)) {
      q_set_neg(&proj->q1, &c->mono[k].coeff);
      divide_aproj_constraint(c, &proj->q1);
    }
    assert(aproj_var_coeff_is_minus_one(c, i));
    assert(aproj_good_constraint(proj, c));

    pvector_push(&proj->neg_vector, c);
  }
}


/*
 * Prepare for elimination of variable i by Fourier-Motzkin or Virtual Term Substitution
 * - i must not have any equality constraints
 * - result:
 *   - all constraints on i are normalized and moved to pos_vector/neg_vector
 *   - they are also all removed from the global constraint set and the 
 *     dependent sets in vtbl
 *   - the set cnstr[i] and counters for i are reset
 *
 * - in every constraint of pos_vector, i has coefficient +1
 *   in every constraint of neg_vector, i has coefficient -1
 *
 */
static void aproj_prepare_inequalities_on_var(arith_projector_t *proj, int32_t i) {
  ptr_set2_t *set;
  aproj_constraint_t *c;
  uint32_t k, n;

  assert(aproj_is_var_to_elim(&proj->vtbl, i) && proj->vtbl.score[i].eq_count == 0);

  // remove constraints from the other vars and from proj->constraints
  aproj_detach_all_constraints_on_var(proj, i);

  assert(proj->pos_vector.size == 0 && proj->neg_vector.size == 0);

  set = proj->vtbl.cnstr[i];
  assert(set != NULL);

  n = set->size;
  for (k=0; k<n; k++) {
    c = set->data[k];
    if (live_ptr_elem(c)) {
      assert(c->tag == APROJ_GE || c->tag == APROJ_GT);
      aproj_normalize_inequality(proj, c, i);
    }
  }

  assert(proj->pos_vector.size == proj->vtbl.score[i].pos_count &&
	 proj->neg_vector.size == proj->vtbl.score[i].neg_count);

  // cleanup
  free_ptr_set2(set);
  aproj_cleanup_var_data(&proj->vtbl, i);
}


/*
 * Combined tag when adding two inequality constraints:
 *   [p > 0]  + [q > 0]  --> [p + q > 0]
 *   [p >= 0] + [q > 0]  --> [p + q > 0]
 *   [p > 0]  + [q >= 0] --> [p + q > 0]
 *   [p >= 0] + [q >= 0] --> [p + q >= 0]
 *
 * We do this using bitwise and (since APROJ_GT = 0b00, APROJ_GE = 0b01).
 *
 * Note: this function also gives the right tag if c1 or c2 is an equality.
 */
static inline aproj_tag_t aproj_combine_tags(aproj_constraint_t *c1, aproj_constraint_t *c2) {
  return c1->tag & c2->tag;
}


/*
 * Resolution: one step in Fourier-Motzkin elimination;
 * - c1 and c2 are two inequality constraints
 * - there's a variable i with coefficient 1 in c1 and -1 in c2
 * - the resolvant is (c1 + c2) > 0 or (c1 + c2 >= 0)
 *   (which does not contain variable i).
 */
static void aproj_resolve(arith_projector_t *proj, aproj_constraint_t *c1, aproj_constraint_t *c2) {
  poly_buffer_t *buffer;

  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  poly_buffer_add_monarray(buffer, c1->mono, c1->nterms);
  poly_buffer_add_monarray(buffer, c2->mono, c2->nterms);
  
  add_constraint_from_buffer(proj, buffer, aproj_combine_tags(c1, c2));
}


/*
 * Free all constraints in vector v then reset v
 */
static void empty_aproj_vector(pvector_t *v) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    free_aproj_constraint(v->data[i]);
  }
  pvector_reset(v);
}


/*
 * Fourier-Motzkin elimination
 */
static void aproj_fourier_motzkin(arith_projector_t *proj, int32_t i) {
  uint32_t j, k, pos, neg;
  pvector_t *v1, *v2;

  aproj_prepare_inequalities_on_var(proj, i);

  v1 = &proj->pos_vector;
  v2 = &proj->neg_vector;

  pos = v1->size;
  neg = v2->size;

  // Add the resolvants
  for (j=0; j<pos; j++) {
    assert(aproj_var_coeff_is_one(v1->data[j], i)); 
    for (k=0; k<neg; k++) {
      assert(aproj_var_coeff_is_minus_one(v2->data[k], i));
      aproj_resolve(proj, v1->data[j], v2->data[k]);
    }
  }

  // Cleanup: delete all constraints in v1 and v2
  empty_aproj_vector(v1);
  empty_aproj_vector(v2);
}


/*
 * VIRTUAL TERM SUBSTITUTION
 */

/*
 * Given a variable i such that pos_count[i] > 0 and neg_count[i] > 0,
 * we first collect and normalize the constraint on i as in Fourier-Motzkin.
 * Every constraint in pos_vector is then of the form (i + p) > 0 or >= 0.
 * Every constraint in neg_vector is of the form (- i + q) > or >= 0.
 *
 * We search for c in pos_vector whose value is minimal in the model and
 * for d in neg_vector whose value is minimal. This gives us two constraints:
 *    c:   (i + p) >= 0
 *    d:  (-i + q) >= 0
 * All constraints on i are true in the model, so we know
 *     - val[p] <= val[i] <= val[q].
 * 
 * We eliminate i by replacing it with the term t := (q - p)/2
 * everywhere.  By the choice of c and d, we known that all
 * constraints on i are satisfied by t in the model.
 */

#if 0
/*
 * Apply the substitution defined by buffer b to constraint c.
 * - i = variable to substitute
 * - i must occur in c
 * - b must be normalized and contain a polynomial of the form i - p
 *   (interpreted as i := p)
 * - b must be distinct from proj->buffer
 *
 * This builds a new constraint that doesn't contain i and add it to proj.
 */
static void aproj_subst_buffer(arith_projector_t *proj, aproj_constraint_t *c, poly_buffer_t *b, int32_t i) {
  poly_buffer_t *buffer;
  rational_t *a;
  int32_t k;

  assert(q_is_one(poly_buffer_var_coeff(b, i)));

  // a := coefficient of i in c
  k = aproj_constraint_find_var(c, i);
  assert(k >= 0);
  q = &proj->q1;
  q_set(a, &c->mono[k].coeff);

  // build c - a * b in buffer
  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  poly_buffer_add_monarray(buffer, c->mono, c->nterms);
  poly_buffer_submul_monarray(buffer, poly_buffer_mono(b), poly_buffer_nterms(b));

  // add the new constraint with the same tag as c
  // this resets buffer
  add_constraint_from_buffer(proj, buffer, c->tag);
}

#endif

/*
 * Apply the substitution defined by b and i to all constraints in
 * pos_vector and neg_vector then remove all constraints in both
 * vectors.
 * - i = variable to eliminate
 * - b must be normalized and contain a polynomial of the form i - t
 *   (interpreted as i := t)
 * - b must be distinct from proj->buffer
 */
static void aproj_substitute_buffer(arith_projector_t *proj, poly_buffer_t *b, int32_t i) {
  pvector_t *v;
  aproj_constraint_t *c;
  poly_buffer_t *buffer;
  monomial_t *b_mono;
  uint32_t k, n, b_nterms;

  assert(q_is_one(poly_buffer_var_coeff(b, i)));

  // buffer for new constraints
  buffer = &proj->buffer;
  assert(poly_buffer_is_zero(buffer));

  // polynomial stored in b
  b_mono = poly_buffer_mono(b);
  b_nterms = poly_buffer_nterms(b);

  v = &proj->pos_vector;
  n = v->size;
  for (k=0; k<n; k++) {
    c = v->data[k];
    assert(aproj_var_coeff_is_one(c, i));
    // c is (i + p) > 0 or >= 0 and b is (i - t)
    // the new constraint is t + p with the same tag as c
    poly_buffer_add_monarray(buffer, c->mono, c->nterms);
    poly_buffer_sub_monarray(buffer, b_mono, b_nterms);

    // add the constraint. This resets buffer
    add_constraint_from_buffer(proj, buffer, c->tag);

    // c is not needed anymore
    free_aproj_constraint(c);
  }
  pvector_reset(v);

  v = &proj->neg_vector;
  n = v->size;
  for (k=0; k<n; k++) {
    c = v->data[k];
    assert(aproj_var_coeff_is_minus_one(c, i));
    // c is (- i + q) > 0 (or >= 0) and b is (i - t)
    // the new constraint is - t + q >0 or >= 0
    poly_buffer_add_monarray(buffer, c->mono, c->nterms);
    poly_buffer_add_monarray(buffer, b_mono, b_nterms);
    // add the constraint. This resets buffer
    add_constraint_from_buffer(proj, buffer, c->tag);

    // c is not needed anymore
    free_aproj_constraint(c);
  }
  pvector_reset(v);
}


/*
 * Find constraint with minimal value in vector v
 * - break ties using the constraint with the smallest id
 */
static aproj_constraint_t *aproj_min_constraint(arith_projector_t *proj, pvector_t *v) {
  rational_t *q_min, *q;
  aproj_constraint_t *min, *c;
  uint32_t i, n;


  n = v->size;
  assert(n > 0);

  q_min = &proj->q1;
  q = &proj->q2;

  min = v->data[0];
  aproj_eval_cnstr_in_model(&proj->vtbl, q_min, min); // q_min = val(min)

  for (i=1; i<n; i++) {
    c = v->data[i];
    aproj_eval_cnstr_in_model(&proj->vtbl, q, c); // q := val(c)

    if (q_lt(q, q_min)) {
      q_set(q_min, q); // q_min := q
      min = c;
    } else if (q_eq(q_min, q) && c->id < min->id) {
      // tie breaking rule: c has lower id than min
      min = c;
    }
  }

  return min;
}

/*
 * Eliminate i by virtual substitution
 */
static void aproj_virtual_subst(arith_projector_t *proj, int32_t i) {
  aproj_constraint_t *pos, *neg;
  poly_buffer_t *b;

  // collect/normalize constraints on i
  aproj_prepare_inequalities_on_var(proj, i);

  pos = aproj_min_constraint(proj, &proj->pos_vector);
  neg = aproj_min_constraint(proj, &proj->neg_vector);

  /*
   * pos->mono is (i + p)
   * neg->mono is (-i + q)
   * we build i + (p - q)/2 in buffer2
   */
  b = &proj->buffer2;
  assert(poly_buffer_is_zero(b));
  poly_buffer_add_monarray(b, pos->mono, pos->nterms);
  poly_buffer_sub_monarray(b, neg->mono, neg->nterms);
  normalize_poly_buffer(b); // b contains 2i + p - q

  q_set_int32(&proj->q1, 1, 2);
  poly_buffer_rescale(b, &proj->q1); // multiply b by 1/2

  assert(poly_buffer_has_var(b, i) && q_is_one(poly_buffer_var_coeff(b, i)));

  aproj_substitute_buffer(proj, b, i);
  reset_poly_buffer(b);
}


/*
 * Main loop: process variables to eliminate one by one
 */
void aproj_eliminate(arith_projector_t *proj) {
  generic_heap_t *var_heap;
  int32_t i;

  var_heap = &proj->vtbl.heap;
  while (! generic_heap_is_empty(var_heap)) {
    i = generic_heap_get_min(var_heap);

#if TRACE
    printf("Eliminating variable %"PRId32"\n", i);
#endif

    switch (aproj_var_group(&proj->vtbl, i)) {
    case APROJ_TRIVIAL:
#if TRACE
      printf(" trivial variable\n");
#endif
      aproj_remove_all_constraints_on_var(proj, i);
      break;

    case APROJ_SUBST:
#if TRACE
      printf(" substitution\n");
#endif
      aproj_elim_var_subst(proj, i);
      break;

    case APROJ_CHEAP:
#if TRACE
      printf(" Fourier-Motzkin\n");
#endif
      aproj_fourier_motzkin(proj, i);
      break;

    case APROJ_EXPENSIVE:
#if TRACE
      printf(" Virtual substitution\n");
#endif
      aproj_virtual_subst(proj, i);
      break;
    }
  }
}


/*
 * CONVERT CONSTRAINTS BACK TO TERMS
 */

/*
 * Convert constraint c to a term
 */
static term_t aproj_convert_constraint(arith_projector_t *proj, aproj_constraint_t *c) {
  rba_buffer_t *buffer;
  aproj_vtbl_t *vtbl;
  uint32_t i, n;
  int32_t x;
  term_t t;

  buffer = term_manager_get_arith_buffer(proj->manager);
  reset_rba_buffer(buffer);

  vtbl = &proj->vtbl;

  n = c->nterms;
  i = 0;
  if (c->mono[0].var == const_idx) {
    // constant
    rba_buffer_add_const(buffer, &c->mono[0].coeff);
    i ++;
  }
  while (i < n) {
    x = c->mono[i].var;
    t = aproj_term_of_var(vtbl, x);
    rba_buffer_add_const_times_term(buffer, proj->terms, &c->mono[i].coeff, t);
    i ++;
  }

  t = NULL_TERM; // prevent GCC warning

  switch (c->tag) {
  case APROJ_GT:
    t = mk_arith_gt0(proj->manager, buffer);
    break;

  case APROJ_GE:
    t = mk_arith_geq0(proj->manager, buffer);
    break;

  case APROJ_EQ:
    t = mk_arith_eq0(proj->manager, buffer);
    break;
  }

  return t;
}


/*
 * Collect the result as a vector of formulas
 * - every constraint in proj->constraint is converted to a Boolean
 *   term that's added to vector v
 * - v is not reset
 *
 * So the set of constraints after in proj->constraint is equivalent to 
 * the conjunction of formulas added to v.
 */
void aproj_get_formula_vector(arith_projector_t *proj, ivector_t *v) {
  ptr_set2_t *set;
  aproj_constraint_t *c;
  uint32_t i, n;
  term_t t;

  set = proj->constraints;
  if (set != NULL) {
    n = set->size;
    for (i=0; i<n; i++) {
      c = set->data[i];
      if (live_ptr_elem(c)) {
	t = aproj_convert_constraint(proj, c);
	ivector_push(v, t);
      }
    }
  }
}


/*
 * Collect the result as a formula:
 * - returns either true_term or a conjunction of arithmetic constraints
 *   that do not contain the eliminated variables.
 */
term_t aproj_get_formula(arith_projector_t *proj) {
  ivector_t v;
  term_t t;

  init_ivector(&v, 10);
  aproj_get_formula_vector(proj, &v);
  t = mk_and(proj->manager, v.size, v.data);
  delete_ivector(&v);

  return t;
}
