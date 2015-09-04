/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * COOPER/PRESBURGER PLAYGROUND
 */
#include <assert.h>

#include "model/presburger.h"
#include "terms/rba_buffer_terms.h"


#define TRACE 1

#if TRACE
#include <inttypes.h>
#include "io/term_printer.h"
#endif

/* PRESBURGER SANITY CHECKER */

//The term_manager enforces the presburger conditions on multiplications.
bool is_presburger_literal(term_table_t *terms, term_t t) {
  bool retval;
  term_t u, k; 
  composite_term_t *args;
  
  switch (term_kind(terms, t)) {

  case ARITH_EQ_ATOM:           //(u = 0)
    u = arith_eq_arg(terms, t);
    retval = is_integer_term(terms, u);
    break;

  case ARITH_GE_ATOM:           //(u >= 0)   
    u = arith_ge_arg(terms, t);
    retval = is_integer_term(terms, u);
    break;
    
  case ARITH_BINEQ_ATOM:        //(u0 = u1)
    args = arith_bineq_atom_desc(terms, t);
    retval = is_integer_term(terms, args->arg[0]) && is_integer_term(terms, args->arg[1]);
    break;
    
  case ARITH_DIVIDES_ATOM:      //±(k | u)
    args = arith_divides_atom_desc(terms, t);
    k = args->arg[0];
    u = args->arg[1];
    retval = is_integer_term(terms, k) && is_integer_term(terms, u);
    break;

  default:
    retval = false;
  }
  
  return retval;
}


/* 
 * Initializes the bounds. Note that a set of constraints need
 * not actually have any such bounds, so they start out NULL.
 */
static void init_cooper(cooper_t *cooper) {

  cooper->glb = NULL;
  q_init(&cooper->glbv);

  cooper->lub = NULL;
  q_init(&cooper->lubv);

  cooper->poly = NULL;

  q_init(&cooper->delta);
  q_set_one(&cooper->delta);

}


/* 
 * This is the same as resetting. Things return to the initial state 
*/
static void delete_cooper(cooper_t *cooper) {

  if (cooper->glb != NULL) {
    free_polynomial(cooper->glb);
    cooper->glb = NULL;
  }
  q_clear(&cooper->glbv);

  if (cooper->lub != NULL) {
    free_polynomial(cooper->lub);
    cooper->lub = NULL;
  }
  q_clear(&cooper->lubv);

  if (cooper->poly != NULL) {
    free_polynomial(cooper->poly);
    cooper->poly = NULL;
  }
  
  q_clear(&cooper->delta);
}


/*
 * CONSTRAINT DESCRIPTORS
 */
#if TRACE
static void print_presburger_monomial(FILE *f, rational_t *coeff, int32_t x, bool first) {
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

static void print_presburger_constraint(FILE *f, presburger_constraint_t *c) {
  uint32_t i, n;
  bool first;

  fprintf(f, "constraint[%"PRIu32"]: (", c->id);
  n = c->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_presburger_monomial(f, &c->mono[i].coeff, c->mono[i].var, first);
      first = false;
    }
  }

  switch (c->tag) {
  case PRES_GT:
    fputs(" > 0)", f);
    break;
  case PRES_GE:
    fputs(" >= 0)", f);
    break;
  case PRES_EQ:
    fputs(" = 0)", f);
    break;
  case PRES_POS_DIVIDES:
    fputs(" = 0 mod ", f);
    q_print_abs(f, c->divisor);
    fputs(")", f);
    break;
  case PRES_NEG_DIVIDES:
    fputs(" != 0 mod ", f);
    q_print_abs(f, c->divisor);
    fputs(")", f);
    break;
  }
}
#endif


/*
 * Create a new constraint from the content of buffer
 * - buffer must be normalized (and non-zero)
 * - tag = constraint type
 * - if tag is a DIVIDES then we initialize the divisor slot
 * Side effect: reset buffer
 */
static presburger_constraint_t *make_presburger_constraint(poly_buffer_t *buffer, presburger_tag_t tag) {
  presburger_constraint_t *tmp;
  monomial_t *p;
  uint32_t i, n;

  n = poly_buffer_nterms(buffer);
  assert(n > 0);
  if (n > MAX_PRESBURGER_CONSTRAINT_SIZE) {
    out_of_memory();
  }
  tmp = (presburger_constraint_t *) safe_malloc(sizeof(presburger_constraint_t) + (n+1) * sizeof(monomial_t));
  tmp->id = 0; // set when it gets added to the constraint pvector
  tmp->tag = tag;
  tmp->nterms = n;
  //if we are a divisor constraint initialize the divisor slot
  if((tag == PRES_POS_DIVIDES) || (tag == PRES_NEG_DIVIDES)){
    tmp->divisor = (rational_t *) safe_malloc(sizeof(rational_t));
    q_init(tmp->divisor);
  } else {
    tmp->divisor = NULL;
  }
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
static void free_presburger_constraint(presburger_constraint_t *c) {
  clear_monarray(c->mono, c->nterms);
  if(c->divisor != NULL){
    q_clear(c->divisor);
    safe_free(c->divisor);
    c->divisor = NULL;	 
  }
  safe_free(c);
}

/*
 * Frees all the constraints in pres, and resets the constraints pvector
 */
static void free_constraints(presburger_t *pres){
  uint32_t i;
  presburger_constraint_t *c;
  pvector_t *constraints;

  constraints = &pres->constraints; 
  for(i = 0; i < constraints->size; i++){
    c = (presburger_constraint_t *) constraints->data[i];
    free_presburger_constraint(c);
  }
  pvector_reset(constraints);
  
}

/*
 * VARIABLE TABLE
 */


/*
 * Initialize table:
 * - n = initial size of arrays variables and values
 * If n is 0, then default size is used.
 */
static void init_presburger_vtbl(presburger_vtbl_t *table, uint32_t n) {
  if (n == 0) {
    n = DEF_PRESBURGER_VTBL_SIZE;
  } 
  
  if (n > MAX_PRESBURGER_VTBL_SIZE) {
    out_of_memory();
  }

  table->nvars = 0;
  table->nelims = 0;
  table->size = n;

  init_ivector(&table->eliminables, 0);
  init_int_hset(&table->elims, 0);
  
  table->variables = (term_t *) safe_malloc(n * sizeof(term_t));
  table->values = (rational_t *) safe_malloc(n * sizeof(rational_t));

  init_int_hmap(&table->vmap, 0);
}


/*
 * Increase the size of arrays variables and values
 */
static void increase_presburger_vtbl_size(presburger_vtbl_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1; // about 50% larger
  if (n > MAX_PRESBURGER_VTBL_SIZE) {
    out_of_memory();
  }
  table->size = n;
  table->variables = (term_t *) safe_realloc(table->variables, n * sizeof(term_t));
  table->values = (rational_t *) safe_realloc(table->values, n * sizeof(rational_t));
}

/*
 * Empty table
 */
static void reset_presburger_vtbl(presburger_vtbl_t *table) {
  uint32_t i, n;

  assert(table->nvars >= 0);

  // free the rationals
  n = table->nvars;
  for (i=0; i<n; i++) {
    q_clear(table->values + i);
  }

  ivector_reset(&table->eliminables);
  int_hset_reset(&table->elims);
  
  int_hmap_reset(&table->vmap);
  
  table->nvars = 0;
  table->nelims = 0;
}


/*
 * Delete
 */
static void delete_presburger_vtbl(presburger_vtbl_t *table) {
  uint32_t i, n;
  
  n = table->nvars;
  for (i=0; i<n; i++) {
    q_clear(table->values + i);
  }

  delete_ivector(&table->eliminables);
  delete_int_hset(&table->elims);
  
  delete_int_hmap(&table->vmap);

  safe_free(table->variables);
  safe_free(table->values);


  table->variables = NULL;
  table->values = NULL;
}


/*
 * Add a new variable x to table
 * - q = value for x
 * - to_elim: if true, x is added to the eliminables and elims
 * - since we don't know all variables yet, we don't add the
 *   mapping from x --> idx in table->vmap.
 */
static void presburger_vtbl_add_var(presburger_vtbl_t *table, term_t x, bool to_elim, rational_t *q) {
  uint32_t i;

  // make room for a new variable
  i = table->nvars;
  if (i == table->size) {
    increase_presburger_vtbl_size(table);
  }
  assert(i < table->size);
  table->nvars = i+1;
  q_init(table->values + i);

  table->variables[i] = x;
  q_set(table->values + i, q);
  
  if (to_elim) {
    assert(!int_hset_member(&table->elims, x));
    table->nelims ++;
    ivector_push(&table->eliminables, x);
    int_hset_add(&table->elims, x);
  }
  
}


/*
 * Complete table: after all variables have been added.
 * - for each variable x, we add the mapping x --> i in table->vmap (where variables[i] = x)
 */
static void close_presburger_vtbl(presburger_vtbl_t *vtbl) {
  int_hmap_pair_t *d;
  uint32_t i, n;
  term_t x;

  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    x = vtbl->variables[i];
    d = int_hmap_get(&vtbl->vmap, x);
    assert(d->val < 0);
    d->val = i;
  }

  int_hset_close(&vtbl->elims);
}


/*
 * Initialize proj
 * - mngr = relevant term manager
 * - n = initial size (total number of variables)
 * - c = number of constraints
 */
void init_presburger_projector(presburger_t *pres, term_manager_t *mngr, uint32_t n, uint32_t c) {
  pres->terms = term_manager_get_terms(mngr);
  pres->manager = mngr;
  init_presburger_vtbl(&pres->vtbl, n);
  init_pvector(&pres->constraints, c);

  init_poly_buffer(&pres->buffer);
}


/*
 * Reset:
 */
void reset_presburger_projector(presburger_t *pres) {
  free_constraints(pres);
  reset_presburger_vtbl(&pres->vtbl);
  pvector_reset(&pres->constraints);
  reset_poly_buffer(&pres->buffer);
}


/*
 * Delete: free memory
 */
void delete_presburger_projector(presburger_t *pres) {
  free_constraints(pres);
  delete_presburger_vtbl(&pres->vtbl);
  delete_pvector(&pres->constraints);
  delete_poly_buffer(&pres->buffer);
}



void presburger_add_var(presburger_t *pres, term_t x, bool to_elim, rational_t *q){
  assert(good_term(pres->terms, x) && pres->constraints.size == 0);
  presburger_vtbl_add_var(&pres->vtbl, x, to_elim, q);
}

/*
 * Close the set of variables and prepare for addition of constraints.
 * - this function must be called once all variables have been added
 *   and before adding the first constraint.
 
 */
void presburger_close_var_set(presburger_t *pres) {
  close_presburger_vtbl(&pres->vtbl);
}

static void presburger_add_cnstr(presburger_t *pres, presburger_constraint_t *c) {
  pvector_t *constraints;

  constraints = &pres->constraints; 
  c->id = constraints->size;
  pvector_push(&pres->constraints, c);
}


static int32_t presburger_index_of_term(presburger_vtbl_t *vtbl, term_t x) {
  int_hmap_pair_t *d;

  d = int_hmap_find(&vtbl->vmap, x);

  assert(d != NULL && d->val >= 0 && d->val < vtbl->nvars);
  return d->val;
}


/*
 * Get value of x in the model.
 */
static inline rational_t *presburger_var_val(presburger_vtbl_t *vtbl, term_t x) {
  int32_t idx = presburger_index_of_term(vtbl, x);
  
  return vtbl->values + idx;
}

static void eval_polynomial_in_model(presburger_vtbl_t *vtbl, rational_t *val, monomial_t* mono, uint32_t nterms) {
  uint32_t i;
  term_t x;
  q_clear(val);
  for (i=0; i<nterms; i++) {
    x = mono[i].var;
    if(x == const_idx){
      q_add(val, &mono[i].coeff);
    } else {
      q_addmul(val, &mono[i].coeff, presburger_var_val(vtbl, x));
    }
  }  
}

/*
 * For debugging: check that the constraint defined by buffer/tag
 * is trivially true.
 */
#ifndef NDEBUG
static bool trivial_constraint_in_buffer(poly_buffer_t *buffer, presburger_tag_t tag, rational_t* divisor) {
  rational_t aux;
  bool r;

  assert(poly_buffer_is_constant(buffer));
  r = false;
  switch (tag) {
  case PRES_GT:
    r = poly_buffer_is_pos_constant(buffer);
    break;
  case PRES_GE:
    r = poly_buffer_is_nonneg_constant(buffer);
    break;
  case PRES_EQ:
    r = poly_buffer_is_zero(buffer);
    break;
  case PRES_POS_DIVIDES:
  case PRES_NEG_DIVIDES:
    q_init(&aux);
    q_set(&aux, &buffer->mono[0].coeff);
    q_integer_rem(&aux, divisor);
    r = q_is_zero(&aux);
    if (tag == PRES_NEG_DIVIDES){ r = !r; }
    break;
  }

  return r;
}

/*
 * Evaluate c->mono in the model
 * - store the result in val
 */
static void presburger_eval_cnstr_in_model(presburger_vtbl_t *vtbl, rational_t *val, presburger_constraint_t *c) {
  eval_polynomial_in_model(vtbl, val, c->mono, c->nterms);
}



/*
 * Check whether c is true in the model
 */
static bool presburger_good_constraint(presburger_t *pres, presburger_constraint_t *c) {
  rational_t aux;
  bool result;
  presburger_tag_t tag;
  
  result = false;
  tag = c->tag;
  
  q_init(&aux);
  presburger_eval_cnstr_in_model(&pres->vtbl, &aux, c);
  switch (tag) {
  case PRES_GE:
    result = q_is_nonneg(&aux);
    break;
  case PRES_GT:
    result = q_is_pos(&aux);
    break;
  case PRES_EQ:
    result = q_is_zero(&aux);
    break;
  case PRES_POS_DIVIDES:
  case PRES_NEG_DIVIDES:
    q_integer_rem(&aux, c->divisor);
    result = q_is_zero(&aux);
    if (tag == PRES_NEG_DIVIDES){ result = !result; }
  }
  q_clear(&aux);
  
  return result;
}

/*
 * Check whether all the constraints are true in the model
 */
static bool presburger_good(presburger_t *pres){
  int32_t i, nconstraints;
  pvector_t *constraints;
  presburger_constraint_t *constraint;
  constraints = &pres->constraints;
  nconstraints = constraints->size;

  //go through the constraints
  for(i = 0; i < nconstraints; i++){
    constraint = (presburger_constraint_t *)constraints->data[i];
    if( ! presburger_good_constraint(pres, constraint) ){ return false; }
  }

  return true;
}


#endif

/*
 * Normalize buffer then build a constraint from its content and add the
 * constraint.
 * - tag = the constraint type.
 */
static void add_constraint_from_buffer(presburger_t *pres, poly_buffer_t *buffer, presburger_tag_t tag, rational_t* divisor) {
  presburger_constraint_t *c;

  normalize_poly_buffer(buffer);
  if (poly_buffer_is_constant(buffer)) {
    // trivial constraint
    assert(trivial_constraint_in_buffer(buffer, tag, divisor));
    reset_poly_buffer(buffer);
  } else {
    c = make_presburger_constraint(buffer, tag);
    if((tag == PRES_POS_DIVIDES) || (tag == PRES_NEG_DIVIDES)){
      assert(divisor != NULL);
      q_set(c->divisor, divisor);
      q_normalize(c->divisor);
      assert(q_is_integer(c->divisor));
    }
    
    assert(presburger_good_constraint(pres, c));

    presburger_add_cnstr(pres, c);
#if TRACE
    printf("--> adding constraint\n");
    print_presburger_constraint(stdout, c);
    printf("\n");
    fflush(stdout);
#endif
  }
}


/*
 * Build and add a constraint
 */
// constraint t == 0
static void presburger_add_var_eq_zero(presburger_t *pres, term_t t) {
  poly_buffer_t *buffer;

  buffer = &pres->buffer;
  assert(poly_buffer_is_zero(buffer));

  poly_buffer_add_var(buffer, t);
  add_constraint_from_buffer(pres, buffer, PRES_EQ, NULL);
}

// constraint t >= 0
static void presburger_add_var_geq_zero(presburger_t *pres, term_t t) {
  poly_buffer_t *buffer;

  buffer = &pres->buffer;
  assert(poly_buffer_is_zero(buffer));

  poly_buffer_add_var(buffer, t);
  add_constraint_from_buffer(pres, buffer, PRES_GE, NULL);
}

// constraint t < 0 (converted to -t > 0)
static void presburger_add_var_lt_zero(presburger_t *pres, term_t t) {
  poly_buffer_t *buffer;

  buffer = &pres->buffer;
  assert(poly_buffer_is_zero(buffer));

  poly_buffer_sub_var(buffer, t);
  add_constraint_from_buffer(pres, buffer, PRES_GT, NULL);
}

// constraint p == 0
static void presburger_add_poly_eq_zero(presburger_t *pres, polynomial_t *p) {
  poly_buffer_t *buffer;

  buffer = &pres->buffer;
  assert(poly_buffer_is_zero(buffer));
  poly_buffer_add_poly(buffer, p);
  add_constraint_from_buffer(pres, buffer, PRES_EQ, NULL);
}

// constraint p >= 0
static void presburger_add_poly_geq_zero(presburger_t *pres, polynomial_t *p) {
  poly_buffer_t *buffer;

  buffer = &pres->buffer;
  assert(poly_buffer_is_zero(buffer));

  poly_buffer_add_poly(buffer, p);
  add_constraint_from_buffer(pres, buffer, PRES_GE, NULL);
}

// constraint p < 0 (converted to -p > 0)
static void presburger_add_poly_lt_zero(presburger_t *pres, polynomial_t *p) {
  poly_buffer_t *buffer;

  buffer = &pres->buffer;
  assert(poly_buffer_is_zero(buffer));

  poly_buffer_sub_poly(buffer, p);
  add_constraint_from_buffer(pres, buffer, PRES_GT, NULL);
}


// constraint (eq t1 t2)
static void presburger_add_arith_bineq(presburger_t *pres, composite_term_t *eq) {
  poly_buffer_t *buffer;
  term_table_t *terms;
  term_t t1, t2;

  assert(eq->arity == 2);
  t1 = eq->arg[0];
  t2 = eq->arg[1];

  buffer = &pres->buffer;
  assert(poly_buffer_is_zero(buffer));

  terms = pres->terms;
  switch (term_kind(terms, t1)) {
  case ARITH_CONSTANT:    
    poly_buffer_add_const(buffer, rational_term_desc(terms, t1));
    break;

  case ARITH_POLY:
    poly_buffer_add_poly(buffer, poly_term_desc(terms, t1));
    break;

  default:
    poly_buffer_add_var(buffer, t1);
    break;
  }

  switch (term_kind(terms, t2)) {
  case ARITH_CONSTANT:    
    poly_buffer_sub_const(buffer, rational_term_desc(terms, t2));
    break;

  case ARITH_POLY:
    poly_buffer_sub_poly(buffer, poly_term_desc(terms, t2));
    break;

  default:
    poly_buffer_sub_var(buffer, t2);
    break;
  }
  add_constraint_from_buffer(pres, buffer, PRES_EQ, NULL);
}

// constraint (t1 | t2) 
static void presburger_add_arith_divides(presburger_t *pres, composite_term_t *divides, bool positive) {
  poly_buffer_t *buffer;
  term_table_t *terms;
  term_t k, u;

  terms = pres->terms;
  
  assert(divides->arity == 2);

  k = divides->arg[0];
  u = divides->arg[1];

  assert(is_constant_term(terms, k) && is_integer_term(terms, k));

  buffer = &pres->buffer;
  assert(poly_buffer_is_zero(buffer));

  switch (term_kind(terms, u)) {
  case ARITH_CONSTANT:
    //FIXME: this should not happen I don't think
    poly_buffer_add_const(buffer, rational_term_desc(terms, u));
    break;

  case ARITH_POLY:
    poly_buffer_add_poly(buffer, poly_term_desc(terms, u));
    break;

  default:
    poly_buffer_add_var(buffer, u);
    break;
  }

  add_constraint_from_buffer(pres, buffer, positive ? PRES_POS_DIVIDES : PRES_NEG_DIVIDES, rational_term_desc(terms, k));
}

/*
 * Add constraint c
 * - c must be an arithmetic predicate of the following forms
 *    (ARITH_EQ_ATOM t)
 *    (ARITH_BINEQ_ATOM t1 t2)
 *    (ARITH_GE_ATOM t)
 *    (NOT (ARITH_GE_ATOM t))
 *    (ARITH_DIVIDES_ATOM k t)
 *    (NOT (ARITH_DIVIDES_ATOM k t))
 *   where t, t1, t2 are either variables declared in pres or linear
 *   polynomials in variables declared in pres, and k is an integer constant.
 * - c must be true in the model specified by calls to presburger_add_var
 * - no variables can be added after this function is called
 *
 * Return code:
 * - 0 means that c was accepted and added to the set of constraints
 * - a negative code means that c is rejected:
 *   - PRES_ERROR_NOT_PRESBURGER_LITERAL means that c is not a presburger literal
 *   - PRES_ERROR_ARITH_DISEQ means that c is either (NOT (ARITH_EQ_ATOM t))
 *                 or (NOT (ARITH_BINEQ_ATOM t1 t2))
 *   - PRES_ERROR_FALSE_ATOM means that c is 'false_term'.
 *
 */

int32_t presburger_add_constraint(presburger_t *pres, term_t c) {
  term_table_t *terms;
  term_t t;
  int32_t code;

  terms = pres->terms;

  assert(good_term(terms, c) && is_boolean_term(terms, c));

  code = 0;
  switch (term_kind(terms, c)) {
  case CONSTANT_TERM:
    // c is either true_term or false_term
    // for true_term, we do nothing
    // for false_term we return an error code.
    if (c == false_term) {
      code = PRES_ERROR_FALSE_LITERAL;
    }
    break;

  case ARITH_EQ_ATOM:
    if (is_neg_term(c)) {
      code = PRES_ERROR_ARITH_DISEQ;
    } else {
      t = arith_eq_arg(terms, c);
      if (term_kind(terms, t) == ARITH_POLY) {
	presburger_add_poly_eq_zero(pres, poly_term_desc(terms, t));
      } else {
	presburger_add_var_eq_zero(pres, t);
      }
    }
    break;

  case ARITH_BINEQ_ATOM:
    if (is_neg_term(c)) {
      code = PRES_ERROR_ARITH_DISEQ;
    } else {
      presburger_add_arith_bineq(pres, arith_bineq_atom_desc(terms, c));
    }
    break;

  case ARITH_GE_ATOM:
    t = arith_ge_arg(terms, c);    
    if (is_pos_term(c)) {
      // atom (t >= 0)
      if (term_kind(terms, t) == ARITH_POLY) {
	presburger_add_poly_geq_zero(pres, poly_term_desc(terms, t));
      } else {
	presburger_add_var_geq_zero(pres, t);
      }
    } else {
      // atom (t < 0)
      if (term_kind(terms, t) == ARITH_POLY) {
	presburger_add_poly_lt_zero(pres, poly_term_desc(terms, t));
      } else {
	presburger_add_var_lt_zero(pres, t);
      }
    }
    break;

  case ARITH_DIVIDES_ATOM:
    if (is_neg_term(c)) {
      presburger_add_arith_divides(pres, arith_divides_atom_desc(terms, c), false);
    } else {
      presburger_add_arith_divides(pres, arith_divides_atom_desc(terms, c), true);
    }
    break;

    
  default:
    code = PRES_ERROR_NOT_PRESBURGER_LITERAL;
    break;
  }

  return code;
}

/*
 * Checks to see if the constraint mentions y, and if so returns true and stores it's coefficient in value.
 * If not returns false, and leaves value untouched.
 * - constraint to check
 * - y a variable
 * - value a non-null pointer to a rational pointer
 */
static bool has_coefficient(presburger_constraint_t *constraint, term_t y, rational_t** value) {
  int32_t i;
  uint32_t nterms;
  term_t var;
  
  assert(value != NULL);

  nterms = constraint->nterms;

  for(i = 0; i < nterms; i++){
    var = constraint->mono[i].var;
    if (var == y){
      *value = &constraint->mono[i].coeff;
      return true;
    }
    if(var > y){  //FIXME: is this correct?
      return false;
    }
  }
  return false;

}


/*
 *  Scales the constraint so that the coefficient of y would be lcm; then sets the
 *  actual coefficient of y to be 1. This is the normalization phase of Cooper's 
 *  algorithm.
 *
 */
static void scale_constraint(presburger_constraint_t *constraint, term_t y, rational_t* lcm) {
  rational_t factor;
  rational_t *aux, *coeff, *divisor;
  int32_t i;
  uint32_t nterms;
  monomial_t *mono;   
  
  //first determine the factor by which we need to multiply by.
  
  if (has_coefficient(constraint, y, &coeff)){
    q_init(&factor);
    q_set(&factor, lcm);
    q_div(&factor, coeff);
    //keep it positive
    if (q_is_neg(&factor)){ q_neg(&factor); }
  }

  nterms = constraint->nterms;
  mono = constraint->mono;
  
  for(i = 0; i < nterms; i++){
    aux = &mono[i].coeff;
    if (mono[i].var == y){
      if (q_is_neg(aux)){
	q_set_minus_one(aux);
      } else {
	q_set_one(aux);
      }
    } else {
      q_mul(aux, &factor);
    }
  }

  //if it is a divibility constraint the divisor needs to be scaled too.
  divisor = constraint->divisor;
  if (divisor != NULL){

    assert((constraint->tag == PRES_POS_DIVIDES) || (constraint->tag == PRES_NEG_DIVIDES));

    q_mul(divisor, &factor);
  }
  
  q_clear(&factor);
}

/* convert all the contraints in pres to the form where the the coeff of
 * y is plus or minus one.
 * - y must be in the eliminables 
 *
 */
static void presburger_normalize(presburger_t *pres, term_t y) {
  rational_t lcm;
  rational_t *rp;
  pvector_t *constraints;
  int32_t yindex, i, nconstraints;
  presburger_constraint_t *constraint;
  poly_buffer_t *buffer;
  presburger_vtbl_t *vtbl;
  
  assert(int_hset_member(&pres->vtbl.elims, y));

  constraints = &pres->constraints;
  nconstraints = constraints->size;
  q_init(&lcm);
  q_set_one(&lcm);

  //pass one: compute the lcm of the coeffs of y
  for(i = 0; i < nconstraints; i++){
    constraint = (presburger_constraint_t *)constraints->data[i];
    rp = NULL;
    if(has_coefficient(constraint, y, &rp)){
      q_lcm(&lcm, rp);
    }
  }
  
  if( ! q_is_one(&lcm)){

    //pass two:
    // scale the constraints accordingly, and set the coefficient of y to 1.
    for(i = 0; i < nconstraints; i++){
      constraint = (presburger_constraint_t *)constraints->data[i];
      scale_constraint(constraint, y, &lcm);
    }
    
    // update the value of y in the vtbl to lcm * old_value
    vtbl = &pres->vtbl;
    yindex = presburger_index_of_term(vtbl, y);
    q_mul(&vtbl->values[yindex], &lcm);
    
    // add the constraint that lcm divides y
    buffer = &pres->buffer;
    assert(poly_buffer_is_zero(buffer));
    poly_buffer_add_var(buffer, y);
    add_constraint_from_buffer(pres, buffer, PRES_POS_DIVIDES, &lcm);

    // assert that all the constraints are still good
    assert(presburger_good(pres));

  }
  
  q_clear(&lcm);
}


static polynomial_t *extract_poly(poly_buffer_t *buffer, const presburger_constraint_t *constraint, term_t y, bool positive, bool isge){
  uint32_t i, nterms;
  term_t var;
  rational_t one;
  
  nterms = constraint->nterms;
  
  q_init(&one);
  q_set_one(&one);
  
  if(positive){
    //subtract all non-y monomials in constraint from the buffer
    for(i = 0; i < nterms; i++){
      var = constraint-> mono[i].var;
      if (var != y){
	poly_buffer_sub_monomial(buffer, var, (rational_t *)&constraint->mono[i].coeff);
      }
    }
    if (isge){ poly_buffer_sub_const(buffer, &one); }
  } else {
    //add all the non-y monomials in constraint to the buffer
    for(i = 0; i < nterms; i++){
      var = constraint->mono[i].var;
      if (var != y){
	poly_buffer_add_monomial(buffer, var, (rational_t *)&constraint->mono[i].coeff);
      }
    }
    if (isge){ poly_buffer_add_const(buffer, &one); }
  }
  q_clear(&one);
  normalize_poly_buffer(buffer);
  return poly_buffer_get_poly(buffer);
}

/*
 * Cooperizes the constraint (leaving it unchanged). Should always return true.
 * If it returns true, then 
 * - kind will contain the form of the cooper term:  
 *   VAR_NONE: y does not occur in the constraint
 *   VAR_LT: y < e  
 *   VAR_GT: e < y  
 *   VAR_EQ: y = e or 
 *   VAR_DV: ±(k | y + r)
 * - in the case of  VAR_LT, VAR_GT, or VAR_EQ poly will contain the corresponding polynomial term e
 * - in the case of VAR_DV  we merely compute q_lcm(lcm, k), thus altering the lcm passed in.
 *
 */
static bool cooperize_constraint(poly_buffer_t *buffer, presburger_constraint_t *constraint, term_t y, cooper_tag_t* kind, polynomial_t **poly, rational_t* lcm){
  presburger_tag_t tag;
  rational_t *coeff;
  bool positive;
    
  assert((kind != NULL) && (poly != NULL) && (lcm != NULL) && q_is_pos(lcm));
  
  if( ! has_coefficient(constraint, y, &coeff)){
    *kind = VAR_NONE;
    return true;
  }

  positive = q_is_pos(coeff);
  
  tag = constraint->tag;
  
  switch(tag){

  case PRES_GT:
  case PRES_GE:
    *kind = positive ? VAR_GT : VAR_LT;
    *poly = extract_poly(buffer, constraint, y, positive, tag == PRES_GE);
    return true;
    
  case PRES_EQ:
    *kind = VAR_EQ;
    *poly = extract_poly(buffer, constraint, y, positive, false);
    return true;

  case PRES_POS_DIVIDES:
  case PRES_NEG_DIVIDES:
    q_lcm(lcm, constraint->divisor);
    *kind = VAR_DV;
    return true;

  default: return false;
  }

  return true;
}



static void presburger_cooperize(presburger_t *pres, term_t y, cooper_t *cooper) {
  poly_buffer_t *buffer;
  pvector_t *constraints;
  int32_t i, nconstraints;
  presburger_constraint_t *constraint;
  cooper_tag_t kind;
  presburger_vtbl_t *vtbl;
  rational_t val;
  polynomial_t *poly;
  
  vtbl = &pres->vtbl;

  buffer = &pres->buffer;
  constraints = &pres->constraints;
  nconstraints = constraints->size;
  
  reset_poly_buffer(buffer);
  
  //go through the constraints
  for(i = 0; i < nconstraints; i++){
    constraint = (presburger_constraint_t *)constraints->data[i];
    if(!cooperize_constraint(buffer, constraint, y, &kind, &poly, &cooper->delta)){
      //shouldn't happen; need to set a flag, cleanup, and exit
      assert(false);
      return;
    }
    switch(kind){

      //nothing to do in these cases
    case VAR_NONE:
    case VAR_DV:
      break;
      
    case VAR_LT:
      // poly is an upper bound
      q_init(&val);
      eval_polynomial_in_model(vtbl, &val, poly->mono, poly->nterms);
      if(cooper->lub == NULL){
	cooper->lub = poly;
	q_set(&cooper->lubv, &val);
      } else {
	if(q_lt(&val, &cooper->lubv)){
	  // poly is the new lub
	  free_polynomial(cooper->lub);
	  cooper->lub = poly;
	  q_set(&cooper->lubv, &val);
	} else {
	  // current lub still good; just clean up
	  free_polynomial(poly);
	  poly = NULL;
	}
      }
      q_clear(&val);
      break;
      
    case VAR_GT:
      // poly is a lower bound
      q_init(&val);
      eval_polynomial_in_model(vtbl, &val, poly->mono, poly->nterms);
      if(cooper->glb == NULL){
	cooper->glb = poly;
	q_set(&cooper->glbv, &val);
      } else {
	if(q_gt(&val, &cooper->glbv)){
	  // poly is the new glb
	  free_polynomial(cooper->glb);
	  cooper->glb = poly;
	  q_set(&cooper->glbv, &val);
	} else {
	  // current glb still good; just clean up
	  free_polynomial(poly);
	  poly = NULL;
	}
      }
      q_clear(&val);
      break;
    
      
    case VAR_EQ:
      // y = poly; our work is almost over
      if(cooper->poly == NULL){
	cooper->poly = poly;
      } else {
	// current exact solution can stay
	free_polynomial(poly);
	poly = NULL;
      }
      break;
      
    default:
      assert(false);
    }
  }
}

static polynomial_t* presburger_solve(presburger_t *pres, term_t y, cooper_t *cooper, rational_t *val){
  poly_buffer_t *solution;
  polynomial_t *result;
  presburger_vtbl_t *vtbl;
  rational_t yval;
  rational_t tmp;
  
  vtbl = &pres->vtbl;
  solution = &pres->buffer;
  
  q_init(&yval);
  q_set(&yval, presburger_var_val(vtbl, y));
 
  reset_poly_buffer(solution);

  if(cooper->poly != NULL){
    //found a trivial solution:  y = poly
    
    poly_buffer_add_poly(solution, cooper->poly);
    q_set(val, &yval);
    
  } else if((cooper->glb == NULL) && (cooper->lub == NULL) && (cooper->poly == NULL)){
    
    //no trivial solution nor upper and lower bounds; need to find a solution near 0.
    if(q_is_neg(&yval)){
      q_sub(val, &yval);
    } else {
      q_add(val, &yval);
    }
    q_integer_rem(val, &cooper->delta);
    poly_buffer_add_const(solution, val);
    
  } else if(cooper->glb != NULL){
    
    //got a lower bound; need to find a solution just above it 
    q_add(val, &yval);
    q_sub(val, &cooper->glbv);
    q_integer_rem(val, &cooper->delta);
    //if val is zero we need to make it delta (or as Dejan suggested search for the smallest?)
    if(q_is_zero(val)){
      q_set(val, &cooper->delta);
    }
    q_add(val, &cooper->glbv);
    
    poly_buffer_add_poly(solution, cooper->glb);
    poly_buffer_add_const(solution, val);
    
  } else {
    
    //got an upper bound; need to find a solution just below it
    q_init(&tmp);
    q_set(&tmp, &cooper->lubv);
    q_set(val, &cooper->lubv);
    q_integer_rem(&tmp, &cooper->delta);
    //if tmp is zero we need to make it delta (or as Dejan suggested search for the smallest?)
    if(q_is_zero(&tmp)){
      q_set(&tmp, &cooper->delta);
    }
    q_sub(val, &tmp);
    
    poly_buffer_add_poly(solution, cooper->lub);
    poly_buffer_sub_const(solution, &tmp);
    
    q_clear(&tmp);
    
  }
  normalize_poly_buffer(solution);
  result = poly_buffer_get_poly(solution);
  return result;
}

/*
 * Replaces all occurrences of the variable y by the polynomial solution in the constraint.
 * If y does not appear ut returns the original constraint. Otherwise it constructs a new one.
 */
static presburger_constraint_t *presburger_subst_in_constraint(presburger_t *pres, term_t y, polynomial_t *solution, presburger_constraint_t *c){
  poly_buffer_t *buffer;
  rational_t *coeff;
  uint32_t i, nterms;
  presburger_constraint_t *retval;
  
  buffer = &pres->buffer;
  reset_poly_buffer(buffer);

  if(has_coefficient(c, y, &coeff)){
    assert(q_is_one(coeff) || q_is_minus_one(coeff));

    nterms = c->nterms;
    for(i = 0; i < nterms; i++){

      if (c->mono[i].var == y){
	if(q_is_one(coeff)){
	  poly_buffer_add_poly(buffer, solution);
	} else {
	  poly_buffer_sub_poly(buffer, solution);
	}
      } else {
	poly_buffer_add_monomial(buffer,  c->mono[i].var, &c->mono[i].coeff);
      }
    }
    normalize_poly_buffer(buffer);
    retval = make_presburger_constraint(buffer, c->tag);
    assert(presburger_good_constraint(pres, retval));
  } else {
    retval = c;
  }
  
  return retval;
}

/*
 * Replaces all occurrences of the variable y by the polynomial solution in the constraints.
 */
static void presburger_subst(presburger_t *pres, term_t y, polynomial_t *solution){
  int32_t i, nconstraints;
  pvector_t *constraints;
  presburger_constraint_t *old_constraint;
  presburger_constraint_t *new_constraint;

  constraints = &pres->constraints;
  nconstraints = constraints->size;

  //go through the constraints
  for(i = 0; i < nconstraints; i++){
    old_constraint = (presburger_constraint_t *)constraints->data[i];
    new_constraint = presburger_subst_in_constraint(pres, y, solution, old_constraint);
    if(old_constraint != new_constraint){  
      constraints->data[i] = new_constraint;
      free_presburger_constraint(old_constraint);
    }
  }
}

/*
 * Apply the variable elimination procedure
 * - no variable or constraint can be added after this function is called.
 */
void presburger_eliminate(presburger_t *pres){
  term_t y;
  ivector_t *eliminables;
  presburger_vtbl_t *vtbl;
  rational_t value_of_solution;
  polynomial_t *solution;
  cooper_t cooper;
  
  vtbl = &pres->vtbl;
  eliminables = &vtbl->eliminables;
  q_init(&value_of_solution);
  
  while(eliminables->size > 0){

    y = ivector_pop2(eliminables);

    //normalize the coefficient of y to be 1
    presburger_normalize(pres, y);

    //go through the constraints and compute the lub, glb and delta.
    init_cooper(&cooper);
    presburger_cooperize(pres, y, &cooper);

    //apply dejan's lemma to obtain a solution
    solution = presburger_solve(pres, y, &cooper, &value_of_solution);


    //eliminate y in favor of the above solution
    presburger_subst(pres, y, solution);
    
    delete_cooper(&cooper);
    
  }
}



/*
 * CONVERT CONSTRAINTS BACK TO TERMS
 */

/*
 * Convert constraint c to a term
 */
static term_t presburger_convert_constraint(presburger_t *pres, presburger_constraint_t *c) {
  rba_buffer_t *buffer;
  uint32_t i, n;
  int32_t x;
  term_t t, k, u;

  buffer = term_manager_get_arith_buffer(pres->manager);
  reset_rba_buffer(buffer);

  n = c->nterms;
  i = 0;
  if (c->mono[0].var == const_idx) {
    // constant
    rba_buffer_add_const(buffer, &c->mono[0].coeff);
    i ++;
  }
  while (i < n) {
    x = c->mono[i].var;
    rba_buffer_add_const_times_term(buffer, pres->terms, &c->mono[i].coeff, x);
    i ++;
  }

  t = NULL_TERM; // prevent GCC warning

  switch (c->tag) {
  case PRES_GT:
    t = mk_arith_gt0(pres->manager, buffer);
    break;

  case PRES_GE:
    t = mk_arith_geq0(pres->manager, buffer);
    break;

  case PRES_EQ:
    t = mk_arith_eq0(pres->manager, buffer);
    break;

  case PRES_POS_DIVIDES:
  case PRES_NEG_DIVIDES:
    k = mk_arith_constant(pres->manager,  c->divisor);
    u = mk_arith_term(pres->manager, buffer);
    t = mk_arith_divides(pres->manager, k, u);
    if (c->tag == PRES_NEG_DIVIDES){
      t = opposite_term(t);
    }
    break;

  }

  return t;
}



/*
 * Collect the result as a vector of formulas
 * - every constraint in pres->constraint is converted to a Boolean
 *   term that's added to vector v
 * - v is not reset
 *
 * So the set of constraints after in pres->constraint is equivalent to 
 * the conjunction of formulas added to v.
 */
void presburger_get_formula_vector(presburger_t *pres, ivector_t *v){
  int32_t i, nconstraints;
  pvector_t *constraints;
  presburger_constraint_t *constraint;
  term_t t;

  constraints = &pres->constraints;
  nconstraints = constraints->size;
  //go through the constraints
  for(i = 0; i < nconstraints; i++){
    constraint = (presburger_constraint_t *)constraints->data[i];
    t = presburger_convert_constraint(pres, constraint);
    ivector_push(v, t);
  }

}


/*
 * Collect the result as a formula:
 * - returns either true_term or a conjunction of arithmetic constraints
 *   that do not contain the eliminated variables.
 */
term_t presburger_get_formula(presburger_t *pres){
  ivector_t v;
  term_t t;

  init_ivector(&v, 10);
  presburger_get_formula_vector(pres, &v);
  t = mk_and(pres->manager, v.size, v.data);
  delete_ivector(&v);

  return t;
}





