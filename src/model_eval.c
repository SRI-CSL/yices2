/*
 * EVALUATION: COMPUTE THE VALUE OF A TERM IN A MODEL
 */

#include <assert.h>
#include <stdbool.h>

#include "model_eval.h"



/*
 * Initialize eval for the given model
 */
void init_evaluator(evaluator_t *eval, model_t *model) {
  eval->model = model;
  eval->terms = model->terms;
  eval->vtbl = &model->vtbl;

  init_int_hmap(&eval->cache, 0); // use the default hmap size
  init_istack(&eval->stack);
  // eval->env is not initialized
}


/*
 * Delete caches and stack
 */
void delete_evaluator(evaluator_t *eval) {
  eval->model = NULL;
  eval->terms = NULL;
  eval->vtbl = NULL;
  delete_int_hmap(&eval->cache);
  delete_istack(&eval->stack);
}



/*
 * Reset: empty the caches and delete all temporary objects
 * created in vtbl.
 */
void reset_evaluator(evaluator_t *eval) {
  value_table_end_tmp(eval->vtbl);
  int_hmap_reset(&eval->cache);
  reset_istack(&eval->stack);
}



/*
 * Get the value mapped to term t in the internal cache
 * - return null_value if nothing is mapped to t
 */
static value_t eval_cached_value(evaluator_t *eval, term_t t) {
  int_hmap_pair_t *r;

  assert(good_term(eval->terms, t));
  
  r = int_hmap_find(&eval->cache, t);
  if (r == NULL) {
    return null_value;
  } else {
    return r->val;
  }
}


/*
 * Add the mapping t := v to the cache
 * - t must not be mapped to an object already
 */
static void eval_cache_map(evaluator_t *eval, term_t t, value_t v) {
  int_hmap_pair_t *r;

  assert(good_term(eval->terms, t) && good_object(eval->vtbl, v));

  r = int_hmap_get(&eval->cache, t);
  assert(r->val < 0);
  r->val = v;
}



/*
 * EVALUATION:
 *
 * Compute the value v of term t in the model 
 * - add the mapping t := v  to the cache
 * - raise an exception if t can't be evaluated
 */
static value_t eval_term(evaluator_t *eval, term_t t);


/*
 * Evaluate terms t[0 ... n-1] and store the result in a[0 .. n-1]
 */
static void eval_term_array(evaluator_t *eval, term_t *t, value_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i] = eval_term(eval, t[i]);
  }
}


/*
 * Evaluate basic constructs
 */
static value_t eval_ite(evaluator_t *eval, composite_term_t *ite) {
  value_t c;

  assert(ite->arity == 3);

  c = eval_term(eval, ite->arg[0]);
  if (is_true(eval->vtbl, c)) {
    return eval_term(eval, ite->arg[1]);
  } else {
    assert(is_false(eval->vtbl, c));
    return eval_term(eval, ite->arg[2]);
  }
}

static value_t eval_eq(evaluator_t *eval, composite_term_t *eq) {
  value_t v1, v2;

  assert(eq->arity == 2);

  v1 = eval_term(eval, eq->arg[0]); 
  v2 = eval_term(eval, eq->arg[1]);
  return vtbl_eval_eq(eval->vtbl, v1, v2);
}


/*
 * app is (fun arg[0] ... arg[n-1]) 
 */ 
static value_t eval_app(evaluator_t *eval, composite_term_t *app) {
  value_t *a;
  value_t *b;
  composite_term_t *update;
  value_t v, f;
  uint32_t n;
  term_t fun;

  // eval the arguments first
  assert(app->arity >= 2);
  n = app->nargs - 1;
  a = alloc_istack_array(&eval->stack, n);
  eval_term_array(eval, app->arg+1, a, n); // a[i] = eval(arg[i])

  /*
   * Try to avoid evaluating fun if it's an update.
   * TODO: check whether that matters??
   */
  fun = app->arg[0];
  if (term_kind(eval->terms, fun) == UPDATE_TERM) {
    b = alloc_istack_array(&eval->stack, n);
    do {
      // fun is (update f (x_1 ... x_n) v)
      update = update_term_desc(eval->terms, fun);
      assert(update->arity == n + 2);

      // evaluate x_1 ... x_n
      eval_term_array(eval, update->arg+1, b, n); // b[i] = eval(x_{i+1})

      // check equality
      v = vtbl_eval_array_eq(eval->vtbl, a, b, n);
      if (is_unknown(eval->vtbl, v)) {
	// result is unknown too
	free_istack_array(&eval->stack, b);
	goto done;

      } else if (is_true(eval->vtbl, v)) {
	// ((update f (x_1 ... x_n) v) a[0] ... a[n-1]) --> v
	v = eval_term(eval, update->arg[n+1]);
	free_istack_array(&eval->stack, b);
	goto done;

      } else {
	// ((update f  ... v) a[0] ... a[n-1]) --> (f a[0] ... a[n-1])
	fun = update->fun;
      }

    } while (term_kind(eval->terms, fun) == UPDATE_TERM);

    free_istack_array(&eval->stack, b);
  }


  /*
   * compute (fun a[0] ... a[n-1])
   */
  assert(term_kind(eval->terms, fun) != UPDATE_TERM);
  f = eval_term(eval, fun);
  v = vtbl_eval_application(eval->vtbl, f, n, a);

 done:
  free_istack_array(&eval->stack, a);
  return v;
}

static value_t eval_or(evaluator_t *eval, composite_term_t *or) {
  uint32_t i, n;
  value_t v;

  n = or->arity;
  for (i=0; i<n; i++) {
    v = eval_term(eval, or->arg[i]);
    if (is_true(eval->vtbl, v)) {
      return v;
    }
    assert(is_false(eval->vtbl, v));
  }

  return vtbl_mk_false(eval->vtbl);
}


static value_t eval_tuple(evaluator_t *eval, composite_term_t *tuple) {
  value_t *a;
  value_t v;
  uint32_t i, n;

  n = tuple->arity;
  a = alloc_istack_array(&eval->stack, n);
  for (i=0; i<n; i++) {
    a[i] = eval_term(eval, tuple->arg[i]);
  }
  v = vtbl_mk_tuple(eval->vtbl, n, a); 
  free_istack_array(&eval->stack, a);

  return v;
}

static value_t eval_select(evaluator_t *eval, select_term_t *select) {
  value_t v;
  value_tuple_t *t;

  v = eval_term(eval, select->arg);
  t = vtbl_tuple(eval->vtbl, v);
  assert(0 <= select->idx && select->idx < t->nelems);

  return t->elem[select->idx];
}

static value_t eval_update(evaluator_t *eval, composite_term_t *update) {
  value_t *a;
  value_t v, f;
  uint32_t i, n;

  assert(update->arity >= 3);

  n = update->arity - 2;
  a = alloc_istack_array(&eval->stack, n);
  f = eval_term(eval, update->arg[0]);
  for (i=0; i<n; i++) {
    a[i] = eval_term(eval, update->arg[i+1]);
  }  
  v = eval_term(eval, update->arg[n+1]);

  v = vtbl_mk_update(eval->vtbl, f, n, a, v);
  free_istack_array(&eval->stack, a);

  return v;
}

static value_t eval_distinct(evaluator_t *eval, composite_term_t *distinct) {
  value_t *a;
  value_t v, eq;
  uint32_t i, j, n;

  n = distinct->arity;
  a = alloc_istack_array(&eval->stack, n);
  for (i=0; i<n; i++) {
    v = eval_term(eval, distinct->arg[i]);

    for (j=0; j<i; j++) {
      eq = vtbl_eval_eq(eval->vtbl, a[j], v);
      if (is_unknown(eval->vtbl, eq)) {
	v = eq; // i.e., unknown
	goto done; 
      } else if (is_true(eval->vtbl, eq)) {
	// a[j] == v so distinct is false
	v = vtbl_mk_false(eval->vtbl);
	goto done;
      }
    }
    a[i] = v;
  }

  v = vtbl_mk_true(eval->vtbl);

 done:
  free_istack_array(&eval->stack, a);
  return v;
}





/*
 * Arithmetic variable: store the value of v in q
 * We don't cache the value of v, because recomputing
 * it should be reasonably cheap. 
 *
 * We may need to change this, if the evaluation requires
 * computing products of large rationals.
 */
static void eval_arith_var(evaluator_t *eval, arith_var_t v, rational_t *q) {
  arithvar_manager_t *m;
  varprod_t *vp;
  uint32_t i, n;
  value_t o;

  m = eval->terms->arith_manager;
  if (arithvar_manager_var_is_primitive(m, v)) {
    o = eval_term(eval, arithvar_manager_term_of_var(m, v));
    q_set(q, vtbl_rational(eval->vtbl, o));

  } else {
    vp = arithvar_manager_var_product(m, v);

    q_set_one(q);
    n = vp->len;
    for (i=0; i<n; i++) {
      v = vp->prod[i].var;
      o = eval_term(eval, arithvar_manager_term_of_var(m, v));
      // prod[i] is v ^ k so q := q * (o ^ k)
      q_mulexp(q, vtbl_rational(eval->vtbl, o), vp->prod[i].exp);
    }
  }
}



/*
 * Arithmetic terms
 */
static value_t eval_arith(evaluator_t *eval, polynomial_t *p) {
  rational_t sum;
  rational_t aux;
  uint32_t i, n;
  arith_var_t x;
  value_t v;

  q_init(&sum); // sum = 0
  q_init(&aux);

  n = p->nterms;
  for (i=0; i<n; i++) {
    x = p->mono[i].var;
    eval_arith_var(eval, x, &aux);
    q_addmul(&sum, &p->mono[i].coeff, &aux); // sum := sum + coeff * aux
  }

  // convert sum to an object
  v = vtbl_mk_rational(eval->vtbl, &sum);

  q_clear(&sum);
  q_clear(&aux);

  return v;
}


// p == 0
static value_t eval_arith_eq(evaluator_t *eval, polynomial_t *p) {
  value_t v;

  v = eval_arith(eval, p);
  return vtbl_mk_bool(eval->vtbl, q_is_zero(vtbl_rational(eval->vtbl, v)));
}

// p>=0
static value_t eval_arith_ge(evaluator_t *eval, polynomial_t *p) {
  value_t v;

  v = eval_arith(eval, p);
  return vtbl_mk_bool(eval->vtbl, q_is_nonneg(vtbl_rational(eval->vtbl, v)));
}

// v1 == v2
static value_t eval_arith_bineq(evaluator_t *eval, arith_bineq_t *eq) {
  value_t v1, v2;

  v1 = eval_term(eval, eq->left);
  v2 = eval_term(eval, eq->right);
  assert(object_is_rational(eval->vtbl, v1) && 
	 object_is_rational(eval->vtbl, v2));

  return vtbl_mk_bool(eval->vtbl, v1 == v2); // because of hash consing
}



/*
 * Nodes in the bit_expr graph
 * - the value is a boolean (not value_t)
 */
static bool eval_node(evaluator_t *eval, node_table_t *table, node_t n);

static bool eval_bit(evaluator_t *eval, node_table_t *table, bit_t b) {
  bool v;

  v = eval_node(eval, table, node_of_bit(b));
  if (bit_is_neg(b)) {
    v = !v;
  }
  return v;
}

// evaluate a variable node n
static term_t eval_var_node(evaluator_t *eval, node_table_t *table, node_t n) {
  bv_var_manager_t *m;
  value_bv_t *bv;
  bv_var_t u;
  value_t v;
  int32_t k;

  assert(is_variable_node(table, n));

  m = eval->terms->bv_manager;
  u = bv_var_of_node(table, n); // bit-vector variable
  k = bv_var_manager_get_index_of_node(m, u, pos_bit(n)); // u[k] = pos_bit(n)
  v = eval_term(eval, bv_var_manager_term_of_var(m, u)); // v = eval term of u

  bv = vtbl_bitvector(eval->vtbl, v);
  assert(0 <= k && k < bv->nbits);
  return bvconst_tst_bit(bv->data, k);
}

static bool eval_node(evaluator_t *eval, node_table_t *table, node_t n) {
  bool b;
  int32_t x;

  assert(good_node(table, n));

  switch (node_kind(table, n)) {
  case CONSTANT_NODE:
    b = true;
    break;

  case VARIABLE_NODE:
    b = eval_var_node(eval, table, n);    
    break;

  case OR_NODE:
    x = eval_cached_node_value(eval, n);
    b = (bool) x;
    if (x < 0) {
      b = eval_bit(eval, table, left_child_of_node(table, n)) ||
	eval_bit(eval, table, right_child_of_node(table, n));
      eval_cache_node_map(eval, n, b);
    }
    break;

  case XOR_NODE:
    x = eval_cached_node_value(eval, n);
    b = (bool) x;
    if (x < 0) {
      b = (eval_bit(eval, table, left_child_of_node(table, n)) !=
	   eval_bit(eval, table, right_child_of_node(table, n)));
      eval_cache_node_map(eval, n, b);
    }
    break;

  default:
    assert(false);
    abort();
    break;
  }

  return b;
}


/*
 * Bitvector terms
 */
static value_t eval_bvconst(evaluator_t *eval, bvconst_term_t *bv) {
  return vtbl_mk_bv_from_bv(eval->vtbl, bv->nbits, bv->bits);
}

static value_t eval_bvlogic(evaluator_t *eval, bvlogic_expr_t *bv) {
  node_table_t *nodes;
  int32_t *a;
  value_t v;
  uint32_t i, n;

  n = bv->nbits;
  a = alloc_istack_array(&eval->stack, n);

  nodes = eval->terms->bv_manager->bm;
  for (i=0; i<n; i++) {
    a[i] = (int32_t) eval_bit(eval, nodes, bv->bit[i]);
  }

  v = vtbl_mk_bv(eval->vtbl, n, a);
  free_istack_array(&eval->stack, a);
  return v;
}


/*
 * Bitvector variable (no caching)
 * - store the value of v into word array a.
 * - p = number of bits in a
 */
static void eval_bitvector_var(evaluator_t *eval, bv_var_t v, uint32_t *a, uint32_t p) {
  bv_var_manager_t *m;
  varprod_t *vp;
  uint32_t i, n, w;
  value_t o;

  w = (p + 31) >> 5; // width of a in words
  m = eval->terms->bv_manager;
  if (bv_var_manager_var_is_primitive(m, v)) {
    o = eval_term(eval, bv_var_manager_term_of_var(m, v));
    bvconst_set(a, w, vtbl_bitvector(eval->vtbl, o)->data);

  } else {
    vp = bv_var_manager_var_product(m, v);

    bvconst_set_one(a, w);
    n = vp->len;
    for (i=0; i<n; i++) {
      v = vp->prod[i].var;
      o = eval_term(eval, bv_var_manager_term_of_var(m, v));

      bvconst_mulpower(a, w, vtbl_bitvector(eval->vtbl, o)->data, vp->prod[i].exp);
    }
  }

  bvconst_normalize(a, p);
}


// bit-vector arithmetic: small coefficients
static value_t eval_bvarith64(evaluator_t *eval, bvarith_expr_t *bv) {
  uint64_t sum;
  uint32_t a[2];
  uint32_t i, n, p;
  bv_var_t x;

  p = bv->size;
  assert(0 < p && p <= 64);

  sum = 0;
  n = bv->nterms;
  for (i=0; i<n; i++) {
    x = bv->mono[i].var;
    a[0] = 0;
    a[1] = 0; // important to set high-order bits to 0
    eval_bitvector_var(eval, x, a, p);    
    sum += bvconst_get64(a) * bv->mono[i].coeff.c;
  }

  // normalize sum: force high-order bits to 0
  sum &= (~((uint64_t) 0)) >> (64 - p);

  // convert sum to a concrete value
  a[0] = (uint32_t) sum; // low-order half of sum
  a[1] = (uint32_t) (sum >> 32); // high-order half of sum
  
  return  vtbl_mk_bv_from_bv(eval->vtbl, p, a);    
}

// bit-vector arithmetic: large coefficients
static value_t eval_bvarith_big(evaluator_t *eval, bvarith_expr_t *bv) {
  uint32_t *sum;
  uint32_t *a;
  uint32_t i, n, p, w;
  bv_var_t x;
  value_t v;

  w = bv->width;
  p = bv->size;
  assert(w >= 3);

  sum = (uint32_t *) alloc_istack_array(&eval->stack, w);
  a = (uint32_t *) alloc_istack_array(&eval->stack, w);
  bvconst_clear(sum, w);

  n = bv->nterms;
  for (i=0; i<n; i++) {
    x = bv->mono[i].var;
    eval_bitvector_var(eval, x, a, p);
    bvconst_addmul(sum, w, a, bv->mono[i].coeff.ptr);
  }

  bvconst_normalize(sum, bv->size);
  v = vtbl_mk_bv_from_bv(eval->vtbl, bv->size, sum);

  free_istack_array(&eval->stack, (int32_t *) a);
  free_istack_array(&eval->stack, (int32_t *) sum);

  return v;
}



static value_t eval_bvarith(evaluator_t *eval, bvarith_expr_t *bv) {
  value_t v;

  if (bv->size <= 64) {
    v = eval_bvarith64(eval, bv);
  } else {
    v = eval_bvarith_big(eval, bv);
  }
  return v;
}


/*
 * Bitvector atoms
 */
static value_t eval_bveq(evaluator_t *eval, bv_atom_t *eq) {
  value_t v1, v2;

  v1 = eval_term(eval, eq->left);
  v2 = eval_term(eval, eq->right);
  assert(object_is_bitvector(eval->vtbl, v1) &&
	 object_is_bitvector(eval->vtbl, v2));

  return vtbl_mk_bool(eval->vtbl, v1 == v2);
}

static value_t eval_bvge(evaluator_t *eval, bv_atom_t *ge) {
  value_t v1, v2;
  value_bv_t *bv1, *bv2;
  bool test;

  v1 = eval_term(eval, ge->left);
  v2 = eval_term(eval, ge->right);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);
  test = bvconst_ge(bv1->data, bv2->data, bv1->nbits);
  return vtbl_mk_bool(eval->vtbl, test);
}

static value_t eval_bvsge(evaluator_t *eval, bv_atom_t *sge) {
  value_t v1, v2;
  value_bv_t *bv1, *bv2;
  bool test;

  v1 = eval_term(eval, sge->left);
  v2 = eval_term(eval, sge->right);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);
  test = bvconst_sge(bv1->data, bv2->data, bv1->nbits);

  return vtbl_mk_bool(eval->vtbl, test);
}




/*
 * Convert bv's value (interpreted as a non-negative integer) into a shift amount. 
 * If bv's value is larger than nbits, then returns bv->nbits
 */
static uint32_t get_shift_amount(value_bv_t *bv) {
  uint32_t n, k, i, s;

  s = bvconst_get32(bv->data); // low-order word = shift amount
  n = bv->nbits;

  if (s < n) {
    k = bv->width;
    // if any of the higher order words is nonzero, return n
    for (i=1; i<k; i++) {
      if (bv->data[i] != 0) { 
	return n;
      }
    }
    return s;
  }
   
  return n;
}


/*
 * General binary bitvector operations
 */
static value_t eval_bvapply(evaluator_t *eval, bvapply_term_t *app) {
  uint32_t *aux;
  uint32_t n, w;
  value_t v1, v2, v;
  value_bv_t *bv1, *bv2;  
  
  v1 = eval_term(eval, app->arg0);
  v2 = eval_term(eval, app->arg1);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);

  n = bv1->nbits;
  w = bv1->width;
  assert(n>0 && w>0);

  aux = (uint32_t *) alloc_istack_array(&eval->stack, w);

  switch (app->op) {
  case BVOP_DIV:
    bvconst_udiv2z(aux, n, bv1->data, bv2->data);
    break;

  case BVOP_REM:
    bvconst_urem2z(aux, n, bv1->data, bv2->data);
    break;

  case BVOP_SDIV:
    bvconst_sdiv2z(aux, n, bv1->data, bv2->data);
    break;

  case BVOP_SREM:
    bvconst_srem2z(aux, n, bv1->data, bv2->data);
    break;

  case BVOP_SMOD:
    bvconst_smod2z(aux, n, bv1->data, bv2->data);
    break;

  case BVOP_SHL:
    bvconst_set(aux, w, bv1->data);
    w = get_shift_amount(bv2);
    bvconst_shift_left(aux, n, w, 0); // padding with 0
    break;

  case BVOP_LSHR:
    bvconst_set(aux, w, bv1->data);
    w = get_shift_amount(bv2);
    bvconst_shift_right(aux, n, w, 0); // padding with 0
    break;

  case BVOP_ASHR:
    bvconst_set(aux, w, bv1->data);
    w = get_shift_amount(bv2);
    bvconst_shift_right(aux, n, w, bvconst_tst_bit(aux, n-1)); // padding with sign bit
    break;

  default:
    assert(false);
    break;
  }

  // convert aux to an object in vtbl
  v = vtbl_mk_bv_from_bv(eval->vtbl, n, aux);

  free_istack_array(&eval->stack, (int32_t *) aux);

  return v;
}



/*
 * Return a default value of type tau
 */
static value_t make_default_value(evaluator_t *eval, type_t tau) {
  type_table_t *types;
  value_t *a;
  value_t v, d;
  uint32_t i, n, w;

  types = eval->terms->type_table;

  switch (type_kind(types, tau)) {
  case BOOL_TYPE:
    v = vtbl_mk_false(eval->vtbl);
    break;

  case INT_TYPE:
  case REAL_TYPE:
    v = vtbl_mk_int32(eval->vtbl, 0);
    break;

  case BITVECTOR_TYPE:
    n = bv_type_size(types, tau);
    w = (n + 31) >> 5; // width 
    a = alloc_istack_array(&eval->stack, w);
    bvconst_clear((uint32_t *) a, w);
    v = vtbl_mk_bv_from_bv(eval->vtbl, n, (uint32_t *) a);
    free_istack_array(&eval->stack, a);
    break;

  case SCALAR_TYPE:
  case UNINTERPRETED_TYPE:
    v = vtbl_mk_const(eval->vtbl, tau, 0, NULL);
    break;

  case TUPLE_TYPE:
    n = tuple_type_ncomponents(types, tau);
    a = alloc_istack_array(&eval->stack, n);
    for (i=0; i<n; i++) {
      a[i] = make_default_value(eval, tuple_type_component(types, tau, i));
    }
    v = vtbl_mk_tuple(eval->vtbl, n, a); 
    free_istack_array(&eval->stack, a);
    break;

  case FUNCTION_TYPE:
    // create a constant function
    d = make_default_value(eval, function_type_range(types, tau));
    v = vtbl_mk_function(eval->vtbl, tau, 0, NULL, d, NULL);
    break;

  case UNUSED_TYPE:
  default:
    // should not happen
    assert(false);
    v = vtbl_mk_unknown(eval->vtbl);
    break;
  }

  return v;
}



/*
 * Uninterpreted term t
 * - t has no concrete value assigned in the model
 * - the model keeps term substitution (in alias_map);
 */
static value_t eval_uninterpreted(evaluator_t *eval, term_t t) {
  term_t u;
  value_t v;

  assert(eval->model->has_alias);
  // check for a substitution
  u = model_find_term_substitution(eval->model, t);
  if (u == NULL_TERM) {
    // assign a default value based on t's type
    v = make_default_value(eval, term_type(eval->terms, t));
  } else {
    // [t --> u] is a substitution in the alias table
    v = eval_term(eval, u);
  }
  
  return v;
}



/*
 * Compute the value v of term t in the model 
 * - add the mapping t := v  to the cache
 * - raise an exception if t can't be evaluated
 */
static value_t eval_term(evaluator_t *eval, term_t t) {
  term_table_t *terms;
  value_t v;

  /*
   * First check the model itself then check the cache.
   * If no value is mapped to t in either of them, compute t's 
   * value v and add the mapping t := v to the cache.
   */
  v = model_find_term_value(eval->model, t);
  if (v == null_value) {
    v = eval_cached_value(eval, t);
    if (v == null_value) {
      terms = eval->terms;

      switch (term_kind(terms, t)) {
      case CONSTANT_TERM:
	if (t == true_term(terms)) {
	  v = vtbl_mk_true(eval->vtbl);
	} else if (t == false_term(terms)) {
	  v = vtbl_mk_false(eval->vtbl); 
	} else {
	  v = vtbl_mk_const(eval->vtbl, term_type(terms, t), constant_term_index(terms, t), 
			    term_name(terms, t));
	}
	break;

      case UNINTERPRETED_TERM:
	// t has no value mapped in the model 
	if (eval->model->has_alias) {
	  v = eval_uninterpreted(eval, t);
	} else {
	  longjmp(eval->env, MDL_EVAL_UNKNOWN_TERM);
	}
	break;

      case VARIABLE:
	// free variable
	longjmp(eval->env, MDL_EVAL_FREEVAR_IN_TERM);
	break;
	
      case NOT_TERM:
	v = eval_term(eval, not_term_arg(terms, t));
	v = vtbl_mk_bool(eval->vtbl, !boolobj_value(eval->vtbl, v));
	break;

      case ITE_TERM:
	v = eval_ite(eval, ite_term_desc(terms, t));
	break;

      case EQ_TERM:
	v = eval_eq(eval, eq_term_desc(terms, t));
	break;

      case APP_TERM:
	v = eval_app(eval, app_term_desc(terms, t));
	break;

      case OR_TERM:
	v = eval_or(eval, or_term_desc(terms, t));
	break;

      case TUPLE_TERM:
	v = eval_tuple(eval, tuple_term_desc(terms, t));
	break;

      case SELECT_TERM:
	v = eval_select(eval, select_term_desc(terms, t));
	break;

      case UPDATE_TERM:
	v = eval_update(eval, update_term_desc(terms, t));
	break;

      case DISTINCT_TERM:
	v = eval_distinct(eval, distinct_term_desc(terms, t));
	break;

      case FORALL_TERM:
	// don't try to evaluate forall for now
	// but we could deal with quantification over finite types
	longjmp(eval->env, MDL_EVAL_QUANTIFIER);
	break;

      case ARITH_TERM:
	v = eval_arith(eval, arith_term_desc(terms, t));
	break;

      case ARITH_EQ_ATOM:
	v = eval_arith_eq(eval, arith_atom_desc(terms, t));
	break;

      case ARITH_GE_ATOM:
	v = eval_arith_ge(eval, arith_atom_desc(terms, t));
	break;

      case ARITH_BINEQ_ATOM:
	v = eval_arith_bineq(eval, arith_bineq_desc(terms, t));
	break;

      case BV_LOGIC_TERM:
	v = eval_bvlogic(eval, bvlogic_term_desc(terms, t));
	break;

      case BV_ARITH_TERM:
	v = eval_bvarith(eval, bvarith_term_desc(terms, t));
	break;

      case BV_CONST_TERM:
	v = eval_bvconst(eval, bvconst_term_desc(terms, t));
	break;

      case BV_EQ_ATOM:
	v = eval_bveq(eval, bvatom_desc(terms, t));
	break;

      case BV_GE_ATOM:
	v = eval_bvge(eval, bvatom_desc(terms, t));
	break;

      case BV_SGE_ATOM:
	v = eval_bvsge(eval, bvatom_desc(terms, t));
	break;

      case BV_APPLY_TERM:
	v = eval_bvapply(eval, bvapply_term_desc(terms, t));
	break;

      default:
	assert(false);
	longjmp(eval->env, MDL_EVAL_INTERNAL_ERROR);
	break;
      }

      // it the result v is unknown we quit now
      if (object_is_unknown(eval->vtbl, v)) {
	longjmp(eval->env, MDL_EVAL_FAILED);
      }

      eval_cache_map(eval, t, v);
    }
  }

  return v;
}




/*
 * Compute the value of t in the model
 * - t must be a valid term
 * - return a negative code if there's an error
 * - otherwise, return the id of a concrete object of eval->model.vtbl
 *
 * Evaluation may create new objects. All these new objects are
 * marked as temporary objects and can be deleted by calling
 * reset_evaluator.
 */
value_t eval_in_model(evaluator_t *eval, term_t t) {
  value_t v;

  v = setjmp(eval->env);
  if (v == 0) {
    v = eval_term(eval, t);
  } else {
    assert(v < 0); // error code after longjmp
    reset_istack(&eval->stack);    
  }

  return v;
}

