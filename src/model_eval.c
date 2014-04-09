/*
 * EVALUATION: COMPUTE THE VALUE OF A TERM IN A MODEL
 */

#include <assert.h>
#include <stdbool.h>

#include "model_eval.h"
#include "bv64_constants.h"


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
 * Bitvector constant: 64bits or less
 */
static value_t eval_bv64_constant(evaluator_t *eval, bvconst64_term_t *c) {
  return vtbl_mk_bv_from_bv64(eval->vtbl, c->bitsize, c->value);
}


/*
 * Bitvector constant
 */
static value_t eval_bv_constant(evaluator_t *eval, bvconst_term_t *c) {
  return vtbl_mk_bv_from_bv(eval->vtbl, c->bitsize, c->data);
}


/*
 * Bitvector terms
 */
static value_t eval_bv_array(evaluator_t *eval, composite_term_t *array) {
  uint32_t i, n;
  int32_t *a;
  value_t v;

  n = array->arity;
  a = alloc_istack_array(&eval->stack, n);
  for (i=0; i<n; i++) {
    v = eval_term(eval, array->arg[i]);
    a[i] = boolobj_value(eval->vtbl, v);
  }

  v = vtbl_mk_bv(eval->vtbl, n, a);

  free_istack_array(&eval->stack, a);

  return v;
}

static value_t eval_bit(evaluator_t *eval, select_term_t *select) {
  value_t v;
  value_bv_t *bv;
  bool b;

  v = eval_term(eval, select->arg);
  bv = vtbl_bitvector(eval->vtbl, v);
  assert(select->idx < bv->nbits);

  b = bvconst_tst_bit(bv->data, select->idx);

  return vtbl_mk_bool(eval->vtbl, b);
}

static term_t eval_bv_div(evaluator_t *eval, composite_term_t *app) {
  uint32_t *aux;
  uint32_t n, w;
  value_t v1, v2, v;
  value_bv_t *bv1, *bv2;

  assert(app->arity == 2);

  v1 = eval_term(eval, app->arg[0]);
  v2 = eval_term(eval, app->arg[1]);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);

  n = bv1->nbits;
  w = bv1->width;
  assert(n>0 && w>0);

  aux = (uint32_t *) alloc_istack_array(&eval->stack, w);
  bvconst_udiv2z(aux, n, bv1->data, bv2->data);
  v = vtbl_mk_bv_from_bv(eval->vtbl, n, aux);

  free_istack_array(&eval->stack, (int32_t *) aux);

  return v;
}

static term_t eval_bv_rem(evaluator_t *eval, composite_term_t *app) {
  uint32_t *aux;
  uint32_t n, w;
  value_t v1, v2, v;
  value_bv_t *bv1, *bv2;

  assert(app->arity == 2);

  v1 = eval_term(eval, app->arg[0]);
  v2 = eval_term(eval, app->arg[1]);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);

  n = bv1->nbits;
  w = bv1->width;
  assert(n>0 && w>0);

  aux = (uint32_t *) alloc_istack_array(&eval->stack, w);
  bvconst_urem2z(aux, n, bv1->data, bv2->data);
  v = vtbl_mk_bv_from_bv(eval->vtbl, n, aux);

  free_istack_array(&eval->stack, (int32_t *) aux);

  return v;
}

static term_t eval_bv_sdiv(evaluator_t *eval, composite_term_t *app) {
  uint32_t *aux;
  uint32_t n, w;
  value_t v1, v2, v;
  value_bv_t *bv1, *bv2;

  assert(app->arity == 2);

  v1 = eval_term(eval, app->arg[0]);
  v2 = eval_term(eval, app->arg[1]);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);

  n = bv1->nbits;
  w = bv1->width;
  assert(n>0 && w>0);

  aux = (uint32_t *) alloc_istack_array(&eval->stack, w);
  bvconst_sdiv2z(aux, n, bv1->data, bv2->data);
  v = vtbl_mk_bv_from_bv(eval->vtbl, n, aux);

  free_istack_array(&eval->stack, (int32_t *) aux);

  return v;
}

static term_t eval_bv_srem(evaluator_t *eval, composite_term_t *app) {
  uint32_t *aux;
  uint32_t n, w;
  value_t v1, v2, v;
  value_bv_t *bv1, *bv2;

  assert(app->arity == 2);

  v1 = eval_term(eval, app->arg[0]);
  v2 = eval_term(eval, app->arg[1]);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);

  n = bv1->nbits;
  w = bv1->width;
  assert(n>0 && w>0);

  aux = (uint32_t *) alloc_istack_array(&eval->stack, w);
  bvconst_srem2z(aux, n, bv1->data, bv2->data);
  v = vtbl_mk_bv_from_bv(eval->vtbl, n, aux);

  free_istack_array(&eval->stack, (int32_t *) aux);

  return v;
}

static term_t eval_bv_smod(evaluator_t *eval, composite_term_t *app) {
  uint32_t *aux;
  uint32_t n, w;
  value_t v1, v2, v;
  value_bv_t *bv1, *bv2;

  assert(app->arity == 2);

  v1 = eval_term(eval, app->arg[0]);
  v2 = eval_term(eval, app->arg[1]);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);

  n = bv1->nbits;
  w = bv1->width;
  assert(n>0 && w>0);

  aux = (uint32_t *) alloc_istack_array(&eval->stack, w);
  bvconst_smod2z(aux, n, bv1->data, bv2->data);
  v = vtbl_mk_bv_from_bv(eval->vtbl, n, aux);

  free_istack_array(&eval->stack, (int32_t *) aux);

  return v;
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
 * Bitvector shift operators
 */
static term_t eval_bv_shl(evaluator_t *eval, composite_term_t *app) {
  uint32_t *aux;
  uint32_t n, w;
  value_t v1, v2, v;
  value_bv_t *bv1, *bv2;

  assert(app->arity == 2);

  v1 = eval_term(eval, app->arg[0]);
  v2 = eval_term(eval, app->arg[1]);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);

  n = bv1->nbits;
  w = bv1->width;
  assert(n>0 && w>0);

  aux = (uint32_t *) alloc_istack_array(&eval->stack, w);
  bvconst_set(aux, w, bv1->data);
  w = get_shift_amount(bv2);
  bvconst_shift_left(aux, n, w, 0); // padding with 0

  v = vtbl_mk_bv_from_bv(eval->vtbl, n, aux);

  free_istack_array(&eval->stack, (int32_t *) aux);

  return v;
}

static term_t eval_bv_lshr(evaluator_t *eval, composite_term_t *app) {
  uint32_t *aux;
  uint32_t n, w;
  value_t v1, v2, v;
  value_bv_t *bv1, *bv2;

  assert(app->arity == 2);

  v1 = eval_term(eval, app->arg[0]);
  v2 = eval_term(eval, app->arg[1]);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);

  n = bv1->nbits;
  w = bv1->width;
  assert(n>0 && w>0);

  aux = (uint32_t *) alloc_istack_array(&eval->stack, w);
  bvconst_set(aux, w, bv1->data);
  w = get_shift_amount(bv2);
  bvconst_shift_right(aux, n, w, 0); // padding with 0

  v = vtbl_mk_bv_from_bv(eval->vtbl, n, aux);

  free_istack_array(&eval->stack, (int32_t *) aux);

  return v;
}

static term_t eval_bv_ashr(evaluator_t *eval, composite_term_t *app) {
  uint32_t *aux;
  uint32_t n, w;
  value_t v1, v2, v;
  value_bv_t *bv1, *bv2;

  assert(app->arity == 2);

  v1 = eval_term(eval, app->arg[0]);
  v2 = eval_term(eval, app->arg[1]);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);

  n = bv1->nbits;
  w = bv1->width;
  assert(n>0 && w>0);

  aux = (uint32_t *) alloc_istack_array(&eval->stack, w);
  bvconst_set(aux, w, bv1->data);
  w = get_shift_amount(bv2);
  bvconst_shift_right(aux, n, w, bvconst_tst_bit(aux, n-1)); // padding with sign bit

  v = vtbl_mk_bv_from_bv(eval->vtbl, n, aux);

  free_istack_array(&eval->stack, (int32_t *) aux);

  return v;
}



/*
 * Bitvector atoms
 */
static value_t eval_bveq(evaluator_t *eval, composite_term_t *eq) {
  value_t v1, v2;

  assert(eq->arity == 2);

  v1 = eval_term(eval, eq->arg[0]);
  v2 = eval_term(eval, eq->arg[1]);
  assert(object_is_bitvector(eval->vtbl, v1) &&
         object_is_bitvector(eval->vtbl, v2));

  return vtbl_mk_bool(eval->vtbl, v1 == v2);
}

static value_t eval_bvge(evaluator_t *eval, composite_term_t *ge) {
  value_t v1, v2;
  value_bv_t *bv1, *bv2;
  bool test;

  assert(ge->arity == 2);

  v1 = eval_term(eval, ge->arg[0]);
  v2 = eval_term(eval, ge->arg[1]);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);
  test = bvconst_ge(bv1->data, bv2->data, bv1->nbits);

  return vtbl_mk_bool(eval->vtbl, test);
}

static value_t eval_bvsge(evaluator_t *eval, composite_term_t *sge) {
  value_t v1, v2;
  value_bv_t *bv1, *bv2;
  bool test;

  assert(sge->arity == 2);

  v1 = eval_term(eval, sge->arg[0]);
  v2 = eval_term(eval, sge->arg[1]);
  bv1 = vtbl_bitvector(eval->vtbl, v1);
  bv2 = vtbl_bitvector(eval->vtbl, v2);
  assert(bv1->nbits == bv2->nbits);
  test = bvconst_sge(bv1->data, bv2->data, bv1->nbits);

  return vtbl_mk_bool(eval->vtbl, test);
}



/*
 * Power product: bitvector of nbits
 */
static value_t eval_bv_pprod(evaluator_t *eval, pprod_t *p, uint32_t nbits) {
  uint32_t *a;
  uint32_t i, n, w;
  term_t t;
  value_t o;

  // get bitsize
  w = (nbits + 31) >> 5; // width in words
  a = (uint32_t *) alloc_istack_array(&eval->stack, w);
  bvconst_set_one(a, w);

  n = p->len;
  for (i=0; i<n; i++) {
    t = p->prod[i].var;
    o = eval_term(eval, t);
    // prod[i] is v ^ k so q := q * (o ^ k)
    bvconst_mulpower(a, w, vtbl_bitvector(eval->vtbl, o)->data, p->prod[i].exp);
  }

  // convert to object
  bvconst_normalize(a, nbits);
  o = vtbl_mk_bv_from_bv(eval->vtbl, nbits, a);

  // cleanup
  free_istack_array(&eval->stack, (int32_t *) a);

  return o;
}


/*
 * Bitvector polynomial: wide coefficients
 */
static value_t eval_bv_poly(evaluator_t *eval, bvpoly_t *p) {
  uint32_t *sum;
  uint32_t i, n, nbits, w;
  term_t t;
  value_t v;

  nbits = p->bitsize;
  w = p->width;

  sum = (uint32_t *) alloc_istack_array(&eval->stack, w);
  bvconst_clear(sum, w);

  n = p->nterms;
  for (i=0; i<n; i++) {
    t = p->mono[i].var;
    if (t == const_idx) {
      bvconst_add(sum, w, p->mono[i].coeff);
    } else {
      v = eval_term(eval, t);
      // sum := sum + coeff * v
      bvconst_addmul(sum, w, p->mono[i].coeff, vtbl_bitvector(eval->vtbl, v)->data);
    }
  }

  // convert sum to an object
  bvconst_normalize(sum, nbits);
  v = vtbl_mk_bv_from_bv(eval->vtbl, nbits, sum);

  free_istack_array(&eval->stack, (int32_t *) sum);

  return v;
}


/*
 * Convert bivector object o to a 64bit unsigned integer
 * - o must have between 1 and 64bits
 */
static uint64_t bvobj_to_uint64(value_bv_t *o) {
  uint64_t c;

  assert(1 <= o->nbits && o->nbits <= 64);
  c = o->data[0];
  if (o->nbits > 32) {
    c += ((uint64_t) o->data[1]) << 32;
  }
  return c;
}


/*
 * Bitvector polynomial: 64bit coefficients
 */
static value_t eval_bv64_poly(evaluator_t *eval, bvpoly64_t *p) {
  uint64_t sum;
  uint32_t i, n, nbits;
  term_t t;
  value_t v;

  nbits = p->bitsize;
  assert(0 < nbits && nbits <= 64);

  sum = 0;

  n = p->nterms;
  for (i=0; i<n; i++) {
    t = p->mono[i].var;
    if (t == const_idx) {
      sum += p->mono[i].coeff;
    } else {
      v = eval_term(eval, t);
      sum += p->mono[i].coeff * bvobj_to_uint64(vtbl_bitvector(eval->vtbl, v));
    }
  }

  // convert sum to an object
  sum = norm64(sum, nbits);
  v = vtbl_mk_bv_from_bv64(eval->vtbl, nbits, sum);

  return v;
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


static value_t eval_xor(evaluator_t *eval, composite_term_t *xor) {
  uint32_t i, n;
  value_t v, w;

  n = xor->arity;
  v = vtbl_mk_false(eval->vtbl);
  for (i=0; i<n; i++) {
    w = eval_term(eval, xor->arg[i]);
    // v := v xor w: true if v != w, false if v == w
    v = vtbl_mk_bool(eval->vtbl, v != w);
  }

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
 * Return a default value of type tau
 */
static value_t make_default_value(evaluator_t *eval, type_t tau) {
  type_table_t *types;
  value_t *a;
  value_t v;
  uint32_t n, w;

  types = eval->terms->types;

  switch (type_kind(types, tau)) {
  case BOOL_TYPE:
    v = vtbl_mk_false(eval->vtbl);
    break;

  case BITVECTOR_TYPE:
    n = bv_type_size(types, tau);
    w = (n + 31) >> 5; // width
    a = alloc_istack_array(&eval->stack, w);
    bvconst_clear((uint32_t *) a, w);
    v = vtbl_mk_bv_from_bv(eval->vtbl, n, (uint32_t *) a);
    free_istack_array(&eval->stack, a);
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
  bool negative;
  value_t v;

  negative = is_neg_term(t);
  t = unsigned_term(t);

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
        if (t == true_term) {
          v = vtbl_mk_true(eval->vtbl);
        } else if (t == false_term) {
          v = vtbl_mk_false(eval->vtbl);
        } else {
          longjmp(eval->env, MDL_EVAL_UNKNOWN_TERM);
        }
        break;

      case BV64_CONSTANT:
        v = eval_bv64_constant(eval, bvconst64_term_desc(terms, t));
        break;

      case BV_CONSTANT:
        v = eval_bv_constant(eval, bvconst_term_desc(terms, t));
        break;

      case UNINTERPRETED_TERM:
        // t has no value mapped in the model
        if (eval->model->has_alias) {
          v = eval_uninterpreted(eval, t);
        } else {
          longjmp(eval->env, MDL_EVAL_UNKNOWN_TERM);
        }
        break;

      case ITE_TERM:
        v = eval_ite(eval, ite_term_desc(terms, t));
        break;

      case EQ_TERM:
        v = eval_eq(eval, eq_term_desc(terms, t));
        break;

      case DISTINCT_TERM:
        v = eval_distinct(eval, distinct_term_desc(terms, t));
        break;

      case OR_TERM:
        v = eval_or(eval, or_term_desc(terms, t));
        break;

      case XOR_TERM:
        v = eval_xor(eval, xor_term_desc(terms, t));
        break;

      case BV_ARRAY:
        v = eval_bv_array(eval, bvarray_term_desc(terms, t));
        break;

      case BV_DIV:
        v = eval_bv_div(eval, bvdiv_term_desc(terms, t));
        break;

      case BV_REM:
        v = eval_bv_rem(eval, bvrem_term_desc(terms, t));
        break;

      case BV_SDIV:
        v = eval_bv_sdiv(eval, bvsdiv_term_desc(terms, t));
        break;

      case BV_SREM:
        v = eval_bv_srem(eval, bvsrem_term_desc(terms, t));
        break;

      case BV_SMOD:
        v = eval_bv_smod(eval, bvsmod_term_desc(terms, t));
        break;

      case BV_SHL:
        v = eval_bv_shl(eval, bvshl_term_desc(terms, t));
        break;

      case BV_LSHR:
        v = eval_bv_lshr(eval, bvlshr_term_desc(terms, t));
        break;

      case BV_ASHR:
        v = eval_bv_ashr(eval, bvashr_term_desc(terms, t));
        break;

      case BV_EQ_ATOM:
        v = eval_bveq(eval, bveq_atom_desc(terms, t));
        break;

      case BV_GE_ATOM:
        v = eval_bvge(eval, bvge_atom_desc(terms, t));
        break;

      case BV_SGE_ATOM:
        v = eval_bvsge(eval, bvsge_atom_desc(terms, t));
        break;

      case BIT_TERM:
        v = eval_bit(eval, bit_term_desc(terms, t));
        break;

      case POWER_PRODUCT:
        assert(is_bitvector_term(terms, t));
	v = eval_bv_pprod(eval, pprod_term_desc(terms, t), term_bitsize(terms, t));
        break;

      case BV64_POLY:
        v = eval_bv64_poly(eval, bvpoly64_term_desc(terms, t));
        break;

      case BV_POLY:
        v = eval_bv_poly(eval, bvpoly_term_desc(terms, t));
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

  if (negative) {
    v = vtbl_mk_not(eval->vtbl, v);
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

