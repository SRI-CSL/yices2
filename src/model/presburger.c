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


#define TRACE 1

#if TRACE
#include <inttypes.h>
#include "io/term_printer.h"
#endif

/* PRESBURGER SANITY CHECKER */

//Currently relying on the parser or literal collector or (?) to enforce the presburger conditions on
//multiplications.
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
    retval = is_constant_term(terms, k) && is_integer_term(terms, k) && is_integer_term(terms, u);
    break;

  default:
    retval = false;
  }
  
  return retval;
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
  p = poly_buffer_mono(buffer);
  for (i=0; i<n; i++) {
    tmp->mono[i].var = p[i].var;
    q_init(&tmp->mono[i].coeff);
    q_set(&tmp->mono[i].coeff, &p[i].coeff);
  }
  tmp->mono[i].var = max_idx; // end marker
  reset_poly_buffer(buffer);

  //if we are a divisor constraint initialize the divisor slot
  if((tag == PRES_POS_DIVIDES) || (tag == PRES_NEG_DIVIDES)){
    tmp->divisor = (rational_t *) safe_malloc(sizeof(rational_t));
    q_init(tmp->divisor);
  }
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
  
  delete_int_hmap(&table->vmap);

  safe_free(table->variables);
  safe_free(table->values);


  table->variables = NULL;
  table->values = NULL;
}


/*
 * Add a new variable x to table
 * - q = value for x
 * - to_elim: if true, x is added to the eliminables
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
    table->nelims ++;
    ivector_push(&table->eliminables, x);
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



/*
 * For debugging: check that the constraint defined by buffer/tag
 * is trivially true.
 */
#ifndef NDEBUG
static bool trivial_constraint_in_buffer(poly_buffer_t *buffer, presburger_tag_t tag) {
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
    r = true; //FIXME
    break;
  }

  return r;
}

/*
 * Check whether c is true in the model
static bool presburger_good_constraint(presburger_t *pres, presburger_constraint_t *c) {
  rational_t aux;
  bool result;

  result = false;

  q_init(&aux);
  presburger_eval_cnstr_in_model(&pres->vtbl, &aux, c);
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
 */

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
    assert(trivial_constraint_in_buffer(buffer, tag));
    reset_poly_buffer(buffer);
  } else {
    c = make_presburger_constraint(buffer, tag);

    if((tag == PRES_POS_DIVIDES) || (tag == PRES_NEG_DIVIDES)){

      assert(divisor != NULL);

      q_set(c->divisor, divisor);

      
    }
    
    //assert(presburger_good_constraint(pres, c));

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
 * Apply the variable elimination procedure
 * - no variable or constraint can be added after this function is called.
 */
void presburger_eliminate(presburger_t *pres){


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
void presburger_get_formula_vector(presburger_t *pres, ivector_t *v){


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





