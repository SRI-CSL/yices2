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
 * EVALUATION: COMPUTE THE VALUE OF A TERM IN A MODEL
 */

#include <assert.h>
#include <stdbool.h>

#include "model/model_eval.h"
#include "terms/bv64_constants.h"


/*
 * Wrapper for q_clear to avoid compilation warnings
 * (some versions of GCC complain about inlining q_clear)
 */
static void clear_rational(rational_t *q) {
  q_clear(q);
}


/*
 * Initialize eval for the given model
 */
void init_evaluator(evaluator_t *eval, model_t *model) {
  eval->model = model;
  eval->terms = model->terms;
  eval->vtbl = &model->vtbl;

  // give default interpretations for the divide by zero
  // functions.
  vtbl_set_default_zero_divide(eval->vtbl);

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
 * Reset: empty the caches
 */
void reset_evaluator(evaluator_t *eval) {
  int_hmap_reset(&eval->cache);
  reset_istack(&eval->stack);
  value_table_start_tmp(eval->vtbl);
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
 * Attempt to get a rational value for v
 * - fails with a longjmp if v is an algebraic number
 */
static rational_t *eval_get_rational(evaluator_t *eval, value_t v) {
  if (object_is_algebraic(eval->vtbl, v)) {
    longjmp(eval->env, MDL_EVAL_FAILED);
  }
  return vtbl_rational(eval->vtbl, v);
}

/*
 * Check whether v is zero: returns false if v is algebraic
 */
static bool eval_is_zero(evaluator_t *eval, value_t v) {
  return object_is_rational(eval->vtbl, v) && q_is_zero(vtbl_rational(eval->vtbl, v));
}

/*
 * Attempt to get a non-zero rational value for v
 * - fails if v is an algebraic number or if it is zero
 */
static rational_t *eval_get_nz_rational(evaluator_t *eval, value_t v) {
  rational_t *q;

  q = eval_get_rational(eval, v);
  if (q_is_zero(q)) {
    longjmp(eval->env, MDL_EVAL_FAILED);
  }
  return q;
}


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
 * Arithmetic atom: t == 0
 */
static value_t eval_arith_eq(evaluator_t *eval, term_t t) {
  value_t v;

  v = eval_term(eval, t);
  return vtbl_mk_bool(eval->vtbl, q_is_zero(eval_get_rational(eval, v)));
}


/*
 * Arithmetic atom: t >= 0
 */
static value_t eval_arith_ge(evaluator_t *eval, term_t t) {
  value_t v;

  v = eval_term(eval, t);
  return vtbl_mk_bool(eval->vtbl, q_is_nonneg(eval_get_rational(eval, v)));
}

/*
 * Arithmetic atom: (is_int t)
 */
static value_t eval_arith_is_int(evaluator_t *eval, term_t t) {
  value_t v;

  v = eval_term(eval, t);
  return vtbl_mk_bool(eval->vtbl, q_is_integer(eval_get_rational(eval, v)));
}


/*
 * Arithmetic term: (floor t)
 */
static value_t eval_arith_floor(evaluator_t *eval, term_t t) {
  rational_t q;
  value_t v;

  v = eval_term(eval, t);
  assert(object_is_rational(eval->vtbl, v));
  
  q_init(&q);
  q_set(&q, eval_get_rational(eval, v)); // q := value of t
  q_floor(&q);
  q_normalize(&q);

  v = vtbl_mk_rational(eval->vtbl, &q);

  clear_rational(&q);

  return v;
}


/*
 * Arithmetic term: (ceil t)
 */
static value_t eval_arith_ceil(evaluator_t *eval, term_t t) {
  rational_t q;
  value_t v;

  v = eval_term(eval, t);
  assert(object_is_rational(eval->vtbl, v));
  
  q_init(&q);
  q_set(&q, eval_get_rational(eval, v)); // q := value of t
  q_ceil(&q);
  q_normalize(&q);

  v = vtbl_mk_rational(eval->vtbl, &q);

  clear_rational(&q);

  return v;
}


/*
 * Arithmetic term: (abs t)
 */
static value_t eval_arith_abs(evaluator_t *eval, term_t t) {
  rational_t q;
  value_t v;

  v = eval_term(eval, t);
  assert(object_is_rational(eval->vtbl, v));
  
  q_init(&q);
  q_set_abs(&q, eval_get_rational(eval, v)); // q := value of t
  q_normalize(&q);

  v = vtbl_mk_rational(eval->vtbl, &q);

  clear_rational(&q);

  return v;
}


/*
 * Arithmetic atom: v1 == v2
 */
static value_t eval_arith_bineq(evaluator_t *eval, composite_term_t *eq) {
  value_t v1, v2;

  assert(eq->arity == 2);

  v1 = eval_term(eval, eq->arg[0]);
  v2 = eval_term(eval, eq->arg[1]);
  assert(object_is_rational(eval->vtbl, v1) &&
         object_is_rational(eval->vtbl, v2));

  return vtbl_mk_bool(eval->vtbl, v1 == v2); // because of hash consing
}


/*
 * Arithmetic term: (/ v1 v2) (division)
 */
static value_t eval_arith_rdiv(evaluator_t *eval, composite_term_t *d) {
  rational_t q;
  value_t v1, v2, o;
  
  assert(d->arity == 2);

  v1 = eval_term(eval, d->arg[0]);
  v2 = eval_term(eval, d->arg[1]);

  if (eval_is_zero(eval, v2)) {
    o = vtbl_eval_rdiv_by_zero(eval->vtbl, v1);
  } else {
    q_init(&q);  
    q_set(&q, eval_get_rational(eval, v1));
    q_div(&q, eval_get_nz_rational(eval, v2));
    q_normalize(&q);
    
    o = vtbl_mk_rational(eval->vtbl, &q);

    clear_rational(&q);
  }


  return o;
}


/*
 * Arithmetic term: (div v1 v2) (integer division)
 */
static value_t eval_arith_idiv(evaluator_t *eval, composite_term_t *d) {
  rational_t q;
  value_t v1, v2, o;
  
  assert(d->arity == 2);

  v1 = eval_term(eval, d->arg[0]);
  v2 = eval_term(eval, d->arg[1]);
  
  if (eval_is_zero(eval, v2)) {
    o = vtbl_eval_idiv_by_zero(eval->vtbl, v1);
  } else {
    q_init(&q);
    q_smt2_div(&q, eval_get_rational(eval, v1), eval_get_nz_rational(eval, v2));
    q_normalize(&q);

    o = vtbl_mk_rational(eval->vtbl, &q);

    clear_rational(&q);
  }

  return o;
}


/*
 * Arithmetic term: (mod v1 v2)
 */
static value_t eval_arith_mod(evaluator_t *eval, composite_term_t *d) {
  rational_t q;
  value_t v1, v2, o;
  
  assert(d->arity == 2);

  v1 = eval_term(eval, d->arg[0]);
  v2 = eval_term(eval, d->arg[1]);

  if (eval_is_zero(eval, v2)) {
    o = vtbl_eval_mod_by_zero(eval->vtbl, v1);
  } else {
    q_init(&q);
    q_smt2_mod(&q, eval_get_rational(eval, v1), eval_get_nz_rational(eval, v2)); 
    q_normalize(&q);

    o = vtbl_mk_rational(eval->vtbl, &q);

    clear_rational(&q);
  }

  return o;
}


/*
 * Arithmetic term: (divides v1 v2)
 */
static value_t eval_arith_divides(evaluator_t *eval, composite_term_t *d) {
  value_t v1, v2;
  bool divides;
  
  assert(d->arity == 2);

  // it's OK for v1 to be zero here.
  v1 = eval_term(eval, d->arg[0]);
  v2 = eval_term(eval, d->arg[1]);
  divides = q_smt2_divides(eval_get_rational(eval, v1), eval_get_rational(eval, v2));

  return vtbl_mk_bool(eval->vtbl, divides);
}


/*
 * Power product: arithmetic
 */
static value_t eval_arith_pprod(evaluator_t *eval, pprod_t *p) {
  rational_t prod;
  uint32_t i, n;
  term_t t;
  value_t o;

  q_init(&prod);
  q_set_one(&prod);

  n = p->len;
  for (i=0; i<n; i++) {
    t = p->prod[i].var;
    o = eval_term(eval, t);
    // prod[i] is v ^ k so q := q * (o ^ k)
    q_mulexp(&prod, eval_get_rational(eval, o), p->prod[i].exp);
  }

  o = vtbl_mk_rational(eval->vtbl, &prod);

  clear_rational(&prod);

  return o;
}


/*
 * Arithmetic polynomial
 */
static value_t eval_arith_poly(evaluator_t *eval, polynomial_t *p) {
  rational_t sum;
  uint32_t i, n;
  term_t t;
  value_t v;

  q_init(&sum); // sum = 0

  n = p->nterms;
  for (i=0; i<n; i++) {
    t = p->mono[i].var;
    if (t == const_idx) {
      q_add(&sum, &p->mono[i].coeff);
    } else {
      v = eval_term(eval, t);
      q_addmul(&sum, &p->mono[i].coeff, eval_get_rational(eval, v)); // sum := sum + coeff * aux
    }
  }

  // convert sum to an object
  v = vtbl_mk_rational(eval->vtbl, &sum);

  clear_rational(&sum);

  return v;
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
  n = app->arity - 1;
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
        fun = update->arg[0];
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
 * Return a default value of type tau
 */
static value_t make_default_value(evaluator_t *eval, type_t tau) {
  return vtbl_make_object(eval->vtbl, tau);
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
          v = vtbl_mk_const(eval->vtbl, term_type(terms, t), constant_term_index(terms, t),
                            term_name(terms, t));
        }
        break;

      case ARITH_CONSTANT:
        v = vtbl_mk_rational(eval->vtbl, rational_term_desc(terms, t));
        break;

      case BV64_CONSTANT:
        v = eval_bv64_constant(eval, bvconst64_term_desc(terms, t));
        break;

      case BV_CONSTANT:
        v = eval_bv_constant(eval, bvconst_term_desc(terms, t));
        break;

      case VARIABLE:
        // free variable
        longjmp(eval->env, MDL_EVAL_FREEVAR_IN_TERM);
        break;

      case UNINTERPRETED_TERM:
        // t has no value mapped in the model
        if (eval->model->has_alias) {
          v = eval_uninterpreted(eval, t);
        } else {
          longjmp(eval->env, MDL_EVAL_UNKNOWN_TERM);
        }
        break;

      case ARITH_EQ_ATOM:
        v = eval_arith_eq(eval, arith_eq_arg(terms, t));
        break;

      case ARITH_GE_ATOM:
        v = eval_arith_ge(eval, arith_ge_arg(terms, t));
        break;

      case ARITH_IS_INT_ATOM:
	v = eval_arith_is_int(eval, arith_is_int_arg(terms, t));
	break;

      case ARITH_FLOOR:
	v = eval_arith_floor(eval, arith_floor_arg(terms, t));
	break;

      case ARITH_CEIL:
	v = eval_arith_ceil(eval, arith_ceil_arg(terms, t));
	break;

      case ARITH_ABS:
	v = eval_arith_abs(eval, arith_abs_arg(terms, t));
	break;

      case ITE_TERM:
      case ITE_SPECIAL:
        v = eval_ite(eval, ite_term_desc(terms, t));
        break;

      case APP_TERM:
        v = eval_app(eval, app_term_desc(terms, t));
        break;

      case UPDATE_TERM:
        v = eval_update(eval, update_term_desc(terms, t));
        break;

      case TUPLE_TERM:
        v = eval_tuple(eval, tuple_term_desc(terms, t));
        break;

      case EQ_TERM:
        v = eval_eq(eval, eq_term_desc(terms, t));
        break;

      case DISTINCT_TERM:
        v = eval_distinct(eval, distinct_term_desc(terms, t));
        break;

      case FORALL_TERM:
        // don't try to evaluate forall for now
        // but we could deal with quantification over finite types
        longjmp(eval->env, MDL_EVAL_QUANTIFIER);
        break;

      case LAMBDA_TERM:
        // don't evaluate
        longjmp(eval->env, MDL_EVAL_LAMBDA);
        break;

      case OR_TERM:
        v = eval_or(eval, or_term_desc(terms, t));
        break;

      case XOR_TERM:
        v = eval_xor(eval, xor_term_desc(terms, t));
        break;

      case ARITH_BINEQ_ATOM:
        v = eval_arith_bineq(eval, arith_bineq_atom_desc(terms, t));
        break;

      case ARITH_RDIV:
	v = eval_arith_rdiv(eval, arith_rdiv_term_desc(terms, t));
	break;

      case ARITH_IDIV:
	v = eval_arith_idiv(eval, arith_idiv_term_desc(terms, t));
	break;

      case ARITH_MOD:
	v = eval_arith_mod(eval, arith_mod_term_desc(terms, t));
	break;

      case ARITH_DIVIDES_ATOM:
	v = eval_arith_divides(eval, arith_divides_atom_desc(terms, t));
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

      case SELECT_TERM:
        v = eval_select(eval, select_term_desc(terms, t));
        break;

      case BIT_TERM:
        v = eval_bit(eval, bit_term_desc(terms, t));
        break;

      case POWER_PRODUCT:
        if (is_bitvector_term(terms, t)) {
          v = eval_bv_pprod(eval, pprod_term_desc(terms, t), term_bitsize(terms, t));
        } else {
          assert(is_arithmetic_term(terms, t));
          v = eval_arith_pprod(eval, pprod_term_desc(terms, t));
        }
        break;

      case ARITH_POLY:
        v = eval_arith_poly(eval, poly_term_desc(terms, t));
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

      // if the result v is unknown we quit now
      assert(v >= 0); // Coverity thinks v can be negative.
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
 * permananet in eval->vtbl.
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


/*
 * Check whether t is true in the model
 * - t must be a valid term
 * - return true if t evaluates to true
 * - return false if t can't be evaluated or
 *   if t's value is not boolean or not true.
 */
bool eval_to_true_in_model(evaluator_t *eval, term_t t) {
  value_t v;

  v = eval_in_model(eval, t);
  return good_object(eval->vtbl, v) && is_true(eval->vtbl, v);
}


/*
 * Check whether t is false in the model
 * - t must be a valid term
 * - return true if t evaluates to true
 * - return false if t can't be evaluated or
 *   if t's value is not boolean or not true.
 */
bool eval_to_false_in_model(evaluator_t *eval, term_t t) {
  value_t v;

  v = eval_in_model(eval, t);
  return good_object(eval->vtbl, v) && is_false(eval->vtbl, v);
}


/*
 * Check whether t is zero in the model
 * - t must be a valid term
 * - if t is an arithmetic term, this checks whether value(t) == 0
 * - if t is a bit-vector term, this checks whether value(t) == 0b0000...
 * - return false if t can't be evaluated, or if t is not an arithemtic
 *   term nor a bitvector term, or if t's value is not zero.
 */
bool eval_to_zero_in_model(evaluator_t *eval, term_t t) {
  value_t v;

  v = eval_in_model(eval, t);
  return good_object(eval->vtbl, v) &&
    (is_zero(eval->vtbl, v) || is_bvzero(eval->vtbl, v));
}

/*
 * Check whether t evaluates to +/-1 in the model
 * - t must be a valid  term
 * - return false if t can't be evaluated or its value is not a rational
 * - return true if t's value is either +1 or -1
 */
bool eval_to_unit_in_model(evaluator_t *eval, term_t t) {
  value_t v;

  v = eval_in_model(eval, t);
  return good_object(eval->vtbl, v) && is_unit(eval->vtbl, v);
}




/*
 * Compute the values of terms a[0 ... n-1]
 * - don't return anything
 * - the value of a[i] can be queried by using eval_in_model(eval, a[i]) later
 *   (this reads the value from eval->cache so that's cheap).
 */
void eval_terms_in_model(evaluator_t *eval, const term_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    (void) eval_in_model(eval, a[i]);
  }
}


/*
 * Check whether term t is useful:
 * - return true if t is unintepreted and has no existing value in eval->model
 *   and is not mapped to another term u in the alias_map
 */
static bool term_is_useful(model_t *model, term_t t) {
  value_t v;

  if (term_kind(model->terms, t) == UNINTERPRETED_TERM) {
    v = model_find_term_value(model, t);
    if (v == null_value && model->has_alias) {
      return model_find_term_substitution(model, t) == NULL_TERM;
    }
  }
  return false;
}

/*
 * Add a mapping t->v in eval->model for every pair (t, v) found in eval->cache
 * and such that t is useful.
 */
void eval_record_useful_terms(evaluator_t *eval) {
  model_t *model;
  int_hmap_t *cache;
  int_hmap_pair_t *r;

  model = eval->model;
  cache = &eval->cache;
  r = int_hmap_first_record(cache);
  while (r != NULL) {
    // r->key is the term, r->val is the value
    if (term_is_useful(model, r->key) && !is_unknown(eval->vtbl, r->val)) {
      model_map_term(model, r->key, r->val);
    }
    r = int_hmap_next_record(cache, r);
  }

}

/*
 * Cached-term collector:
 * - call f(aux, t) for every t that's stored in eval->cache
 *   if f(aux, t) returns true, add t to v
 * - f must not have side effects
 */
void evaluator_collect_cached_terms(evaluator_t *eval, void *aux, model_filter_t f, ivector_t *v) {
  int_hmap_t *cache;
  int_hmap_pair_t *r;

  cache = &eval->cache;
  r = int_hmap_first_record(cache);
  while (r != NULL) {
    if (f(aux, r->key)) {
      ivector_push(v, r->key);
    }
    r = int_hmap_next_record(cache, r);
  }
}
