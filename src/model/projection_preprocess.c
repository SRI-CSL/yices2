/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2026 SRI International.
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
 * RDIV elimination for projection.
 *
 * This rewrites RDIV-containing arithmetic literals in a model-true cube into
 * RDIV-free arithmetic literals plus model-sign guards. It runs after
 * get_implicant has selected model branches.
 */

#include <assert.h>
#include <stdbool.h>

#include "model/concrete_values.h"
#include "model/model_eval.h"
#include "model/projection_preprocess.h"
#include "terms/rba_buffer_terms.h"
#include "terms/terms.h"
#include "utils/int_hash_map.h"
#include "utils/memalloc.h"

#ifdef HAVE_MCSAT
#include "poly/algebraic_number.h"
#endif


typedef enum {
  RDIV_SIGN_NEG = -1,
  RDIV_SIGN_ZERO = 0,
  RDIV_SIGN_POS = 1,
} rdiv_sign_t;

typedef enum {
  RDIV_ATOM_EQ,
  RDIV_ATOM_NEQ,
  RDIV_ATOM_GEQ,
  RDIV_ATOM_LT,
} rdiv_atom_kind_t;

typedef struct rdiv_cache_entry_s {
  proj_flag_t code;
  int32_t extra_error;
  ivector_t lits;
} rdiv_cache_entry_t;

struct rdiv_preprocess_cache_s {
  model_t *mdl;
  term_manager_t *mngr;
  term_table_t *terms;
  evaluator_t eval;
  int_hmap_t map;
  rdiv_cache_entry_t *data;
  uint32_t size;
  uint32_t capacity;
};

typedef rdiv_preprocess_cache_t rdiv_preproc_t;

typedef struct rdiv_frac_s {
  term_t num;
  term_t den;
  ivector_t guards;
} rdiv_frac_t;


static proj_flag_t rewrite_literal_rdiv(rdiv_preproc_t *p, term_t lit, ivector_t *out, int32_t *extra_error);


/*
 * Rewrite cache
 */

static void extend_rdiv_preprocess_cache(rdiv_preprocess_cache_t *cache) {
  uint32_t n;

  n = cache->capacity;
  if (n == 0) {
    n = 16;
  } else {
    if (n > INT32_MAX/2) {
      out_of_memory();
    }
    n <<= 1;
  }
  cache->data = (rdiv_cache_entry_t *) safe_realloc(cache->data, n * sizeof(rdiv_cache_entry_t));
  cache->capacity = n;
}

rdiv_preprocess_cache_t *new_rdiv_preprocess_cache(model_t *mdl, term_manager_t *mngr) {
  rdiv_preprocess_cache_t *cache;

  cache = (rdiv_preprocess_cache_t *) safe_malloc(sizeof(rdiv_preprocess_cache_t));
  cache->mdl = mdl;
  cache->mngr = mngr;
  cache->terms = mngr->terms;
  assert(cache->terms == mdl->terms);

  init_evaluator(&cache->eval, mdl);
  init_int_hmap(&cache->map, 0);
  cache->data = NULL;
  cache->size = 0;
  cache->capacity = 0;

  return cache;
}

void delete_rdiv_preprocess_cache(rdiv_preprocess_cache_t *cache) {
  uint32_t i, n;

  n = cache->size;
  for (i=0; i<n; i++) {
    delete_ivector(&cache->data[i].lits);
  }
  safe_free(cache->data);
  delete_int_hmap(&cache->map);
  delete_evaluator(&cache->eval);
  safe_free(cache);
}

static bool cached_rdiv_rewrite(rdiv_preprocess_cache_t *cache, term_t lit,
                                ivector_t *out, int32_t *extra_error, proj_flag_t *code) {
  int_hmap_pair_t *p;
  rdiv_cache_entry_t *entry;

  if (lit < 0) {
    return false;
  }

  p = int_hmap_find(&cache->map, lit);
  if (p == NULL) {
    return false;
  }

  assert(0 <= p->val && p->val < (int32_t) cache->size);
  entry = cache->data + p->val;
  *code = entry->code;
  if (entry->code == PROJ_NO_ERROR) {
    ivector_add(out, entry->lits.data, entry->lits.size);
  } else {
    *extra_error = entry->extra_error;
  }
  return true;
}

static void cache_rdiv_rewrite(rdiv_preprocess_cache_t *cache, term_t lit,
                               proj_flag_t code, int32_t extra_error, const ivector_t *lits) {
  rdiv_cache_entry_t *entry;
  uint32_t k;

  if (lit < 0) {
    return;
  }

  if (cache->size == cache->capacity) {
    extend_rdiv_preprocess_cache(cache);
  }

  k = cache->size;
  assert(k < (uint32_t) INT32_MAX);
  cache->size = k + 1;

  entry = cache->data + k;
  entry->code = code;
  entry->extra_error = extra_error;
  init_ivector(&entry->lits, lits->size);
  if (code == PROJ_NO_ERROR) {
    ivector_add(&entry->lits, lits->data, lits->size);
  }

  int_hmap_add(&cache->map, lit, (int32_t) k);
}


/*
 * Arithmetic builders
 */

static term_t arith_const(rdiv_preproc_t *p, const rational_t *q) {
  rational_t tmp;
  term_t t;

  q_init(&tmp);
  q_set(&tmp, q);
  t = mk_arith_constant(p->mngr, &tmp);
  q_clear(&tmp);

  return t;
}

static term_t arith_one(rdiv_preproc_t *p) {
  rational_t q;
  term_t t;

  q_init(&q);
  q_set_one(&q);
  t = mk_arith_constant(p->mngr, &q);
  q_clear(&q);

  return t;
}

static term_t arith_add(rdiv_preproc_t *p, term_t a, term_t b) {
  rba_buffer_t *buffer;

  buffer = term_manager_get_arith_buffer(p->mngr);
  reset_rba_buffer(buffer);
  rba_buffer_add_term(buffer, p->terms, a);
  rba_buffer_add_term(buffer, p->terms, b);

  return mk_arith_term(p->mngr, buffer);
}

static term_t arith_sub(rdiv_preproc_t *p, term_t a, term_t b) {
  rba_buffer_t *buffer;

  buffer = term_manager_get_arith_buffer(p->mngr);
  reset_rba_buffer(buffer);
  rba_buffer_add_term(buffer, p->terms, a);
  rba_buffer_sub_term(buffer, p->terms, b);

  return mk_arith_term(p->mngr, buffer);
}

static term_t arith_mul(rdiv_preproc_t *p, term_t a, term_t b) {
  rba_buffer_t *buffer;

  buffer = term_manager_get_arith_buffer(p->mngr);
  reset_rba_buffer(buffer);
  rba_buffer_add_term(buffer, p->terms, a);
  rba_buffer_mul_term(buffer, p->terms, b);

  return mk_arith_term(p->mngr, buffer);
}

static term_t arith_mul_const(rdiv_preproc_t *p, const rational_t *q, term_t a) {
  rational_t tmp;
  rba_buffer_t *buffer;
  term_t t;

  q_init(&tmp);
  q_set(&tmp, q);
  buffer = term_manager_get_arith_buffer(p->mngr);
  reset_rba_buffer(buffer);
  rba_buffer_add_const_times_term(buffer, p->terms, &tmp, a);
  t = mk_arith_term(p->mngr, buffer);
  q_clear(&tmp);

  return t;
}


/*
 * Fractions
 */

static void init_rdiv_frac(rdiv_frac_t *f) {
  f->num = NULL_TERM;
  f->den = NULL_TERM;
  init_ivector(&f->guards, 0);
}

static void delete_rdiv_frac(rdiv_frac_t *f) {
  delete_ivector(&f->guards);
}

static void frac_of_term(rdiv_preproc_t *p, term_t t, rdiv_frac_t *out) {
  init_rdiv_frac(out);
  out->num = t;
  out->den = arith_one(p);
}

static void frac_of_const(rdiv_preproc_t *p, const rational_t *q, rdiv_frac_t *out) {
  frac_of_term(p, arith_const(p, q), out);
}

static void frac_zero(rdiv_preproc_t *p, rdiv_frac_t *out) {
  frac_of_term(p, zero_term, out);
}

static void frac_one(rdiv_preproc_t *p, rdiv_frac_t *out) {
  frac_of_term(p, arith_one(p), out);
}

static void frac_add_guards(rdiv_frac_t *out, const rdiv_frac_t *a, const rdiv_frac_t *b) {
  ivector_add(&out->guards, a->guards.data, a->guards.size);
  ivector_add(&out->guards, b->guards.data, b->guards.size);
}

static void frac_add(rdiv_preproc_t *p, const rdiv_frac_t *a, const rdiv_frac_t *b, rdiv_frac_t *out) {
  init_rdiv_frac(out);
  out->num = arith_add(p, arith_mul(p, a->num, b->den), arith_mul(p, b->num, a->den));
  out->den = arith_mul(p, a->den, b->den);
  frac_add_guards(out, a, b);
}

static void frac_sub(rdiv_preproc_t *p, const rdiv_frac_t *a, const rdiv_frac_t *b, rdiv_frac_t *out) {
  init_rdiv_frac(out);
  out->num = arith_sub(p, arith_mul(p, a->num, b->den), arith_mul(p, b->num, a->den));
  out->den = arith_mul(p, a->den, b->den);
  frac_add_guards(out, a, b);
}

static void frac_mul(rdiv_preproc_t *p, const rdiv_frac_t *a, const rdiv_frac_t *b, rdiv_frac_t *out) {
  init_rdiv_frac(out);
  out->num = arith_mul(p, a->num, b->num);
  out->den = arith_mul(p, a->den, b->den);
  frac_add_guards(out, a, b);
}

static void frac_mul_const(rdiv_preproc_t *p, const rational_t *q, rdiv_frac_t *f) {
  f->num = arith_mul_const(p, q, f->num);
}


/*
 * Structural RDIV detection
 */

static bool pprod_contains_rdiv(rdiv_preproc_t *p, pprod_t *prod);

static bool term_contains_rdiv(rdiv_preproc_t *p, term_t t) {
  composite_term_t *d;
  polynomial_t *poly;
  term_kind_t kind;
  uint32_t i, n;

  t = unsigned_term(t);
  kind = term_kind(p->terms, t);

  switch (kind) {
  case ARITH_RDIV:
    return true;

  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
    return term_contains_rdiv(p, arith_atom_arg(p->terms, t));

  case ARITH_POLY:
    poly = poly_term_desc(p->terms, t);
    n = poly->nterms;
    for (i=0; i<n; i++) {
      if (poly->mono[i].var != const_idx &&
          term_contains_rdiv(p, poly->mono[i].var)) {
        return true;
      }
    }
    return false;

  case POWER_PRODUCT:
    return pprod_contains_rdiv(p, pprod_term_desc(p->terms, t));

  case ARITH_IS_INT_ATOM:
  case ARITH_FLOOR:
  case ARITH_CEIL:
  case ARITH_ABS:
    return term_contains_rdiv(p, unary_term_arg(p->terms, t));

  case SELECT_TERM:
    return term_contains_rdiv(p, select_term_arg(p->terms, t));

  case BIT_TERM:
    return term_contains_rdiv(p, bit_term_arg(p->terms, t));

  case ITE_TERM:
  case ITE_SPECIAL:
  case APP_TERM:
  case UPDATE_TERM:
  case TUPLE_TERM:
  case EQ_TERM:
  case DISTINCT_TERM:
  case FORALL_TERM:
  case LAMBDA_TERM:
  case OR_TERM:
  case XOR_TERM:
  case ARITH_BINEQ_ATOM:
  case ARITH_IDIV:
  case ARITH_MOD:
  case ARITH_DIVIDES_ATOM:
  case ARITH_FF_BINEQ_ATOM:
  case BV_ARRAY:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
    d = composite_term_desc(p->terms, t);
    n = d->arity;
    for (i=0; i<n; i++) {
      if (term_contains_rdiv(p, d->arg[i])) {
        return true;
      }
    }
    return false;

  default:
    return false;
  }
}

static bool pprod_contains_rdiv(rdiv_preproc_t *p, pprod_t *prod) {
  uint32_t i, n;

  if (pp_is_empty(prod)) {
    return false;
  }
  if (pp_is_var(prod)) {
    return term_contains_rdiv(p, var_of_pp(prod));
  }

  n = prod->len;
  for (i=0; i<n; i++) {
    if (term_contains_rdiv(p, prod->prod[i].var)) {
      return true;
    }
  }
  return false;
}


/*
 * Model signs
 */

static proj_flag_t model_sign_and_guard(rdiv_preproc_t *p, term_t t, rdiv_sign_t *sign, term_t *guard, int32_t *extra_error) {
  value_t v;
  int32_t sgn;

  assert(is_arithmetic_term(p->terms, t));

  if (term_kind(p->terms, t) == ARITH_CONSTANT) {
    sgn = q_sgn(rational_term_desc(p->terms, t));
  } else {
    v = eval_in_model(&p->eval, t);
    if (v < 0) {
      *extra_error = v;
      return PROJ_ERROR_IN_EVAL;
    }

    if (object_is_rational(&p->mdl->vtbl, v)) {
      sgn = q_sgn(vtbl_rational(&p->mdl->vtbl, v));
    } else {
#ifdef HAVE_MCSAT
      assert(object_is_algebraic(&p->mdl->vtbl, v));
      sgn = lp_algebraic_number_sgn(vtbl_algebraic_number(&p->mdl->vtbl, v));
#else
      *extra_error = v;
      return PROJ_ERROR_IN_EVAL;
#endif
    }
  }

  if (sgn > 0) {
    *sign = RDIV_SIGN_POS;
    *guard = (term_kind(p->terms, t) == ARITH_CONSTANT) ? true_term : mk_arith_term_gt0(p->mngr, t);
  } else if (sgn < 0) {
    *sign = RDIV_SIGN_NEG;
    *guard = (term_kind(p->terms, t) == ARITH_CONSTANT) ? true_term : mk_arith_term_lt0(p->mngr, t);
  } else {
    *sign = RDIV_SIGN_ZERO;
    *guard = true_term;
  }

  return PROJ_NO_ERROR;
}


/*
 * Fractionization
 */

static proj_flag_t fraction_of_arith(rdiv_preproc_t *p, term_t t, rdiv_frac_t *out, int32_t *extra_error);

static proj_flag_t fraction_pow(rdiv_preproc_t *p, const rdiv_frac_t *base, uint32_t exp, rdiv_frac_t *out, int32_t *extra_error) {
  rdiv_frac_t acc, tmp;
  uint32_t i;

  (void) extra_error;

  frac_one(p, &acc);
  for (i=0; i<exp; i++) {
    frac_mul(p, &acc, base, &tmp);
    delete_rdiv_frac(&acc);
    acc = tmp;
  }

  *out = acc;
  return PROJ_NO_ERROR;
}

static proj_flag_t fraction_of_poly(rdiv_preproc_t *p, term_t t, rdiv_frac_t *out, int32_t *extra_error) {
  polynomial_t *poly;
  term_t *var;
  rational_t *coeff;
  rdiv_frac_t acc, mono, tmp;
  uint32_t i, n;
  proj_flag_t code;

  poly = poly_term_desc(p->terms, t);
  n = poly->nterms;

  var = NULL;
  coeff = NULL;
  if (n > 0) {
    var = (term_t *) safe_malloc(n * sizeof(term_t));
    coeff = (rational_t *) safe_malloc(n * sizeof(rational_t));
    for (i=0; i<n; i++) {
      var[i] = poly->mono[i].var;
      q_init(&coeff[i]);
      q_set(&coeff[i], &poly->mono[i].coeff);
    }
  }

  frac_zero(p, &acc);
  code = PROJ_NO_ERROR;

  for (i=0; i<n; i++) {
    if (var[i] == const_idx) {
      frac_of_const(p, &coeff[i], &mono);
    } else {
      code = fraction_of_arith(p, var[i], &mono, extra_error);
      if (code != PROJ_NO_ERROR) {
        goto done;
      }
      frac_mul_const(p, &coeff[i], &mono);
    }

    frac_add(p, &acc, &mono, &tmp);
    delete_rdiv_frac(&acc);
    delete_rdiv_frac(&mono);
    acc = tmp;
  }

 done:
  for (i=0; i<n; i++) {
    q_clear(&coeff[i]);
  }
  safe_free(coeff);
  safe_free(var);

  if (code == PROJ_NO_ERROR) {
    *out = acc;
  } else {
    delete_rdiv_frac(&acc);
  }

  return code;
}

static proj_flag_t fraction_of_pprod(rdiv_preproc_t *p, pprod_t *prod, rdiv_frac_t *out, int32_t *extra_error) {
  varexp_t *factor;
  rdiv_frac_t acc, base, pow, tmp;
  uint32_t i, n;
  proj_flag_t code;

  if (pp_is_empty(prod)) {
    frac_one(p, out);
    return PROJ_NO_ERROR;
  }

  if (pp_is_var(prod)) {
    return fraction_of_arith(p, var_of_pp(prod), out, extra_error);
  }

  n = prod->len;
  factor = NULL;
  if (n > 0) {
    factor = (varexp_t *) safe_malloc(n * sizeof(varexp_t));
    for (i=0; i<n; i++) {
      factor[i] = prod->prod[i];
    }
  }

  frac_one(p, &acc);
  code = PROJ_NO_ERROR;

  for (i=0; i<n; i++) {
    code = fraction_of_arith(p, factor[i].var, &base, extra_error);
    if (code != PROJ_NO_ERROR) {
      goto done;
    }

    code = fraction_pow(p, &base, factor[i].exp, &pow, extra_error);
    delete_rdiv_frac(&base);
    if (code != PROJ_NO_ERROR) {
      goto done;
    }

    frac_mul(p, &acc, &pow, &tmp);
    delete_rdiv_frac(&acc);
    delete_rdiv_frac(&pow);
    acc = tmp;
  }

 done:
  safe_free(factor);

  if (code == PROJ_NO_ERROR) {
    *out = acc;
  } else {
    delete_rdiv_frac(&acc);
  }

  return code;
}

static proj_flag_t fraction_of_rdiv(rdiv_preproc_t *p, term_t t, rdiv_frac_t *out, int32_t *extra_error) {
  composite_term_t *d;
  rdiv_frac_t lhs, rhs;
  rdiv_sign_t sign;
  term_t arg0, arg1, guard;
  proj_flag_t code;

  d = arith_rdiv_term_desc(p->terms, t);
  assert(d->arity == 2);
  arg0 = d->arg[0];
  arg1 = d->arg[1];

  code = fraction_of_arith(p, arg0, &lhs, extra_error);
  if (code != PROJ_NO_ERROR) {
    return code;
  }

  code = fraction_of_arith(p, arg1, &rhs, extra_error);
  if (code != PROJ_NO_ERROR) {
    delete_rdiv_frac(&lhs);
    return code;
  }

  code = model_sign_and_guard(p, rhs.num, &sign, &guard, extra_error);
  if (code != PROJ_NO_ERROR) {
    goto done;
  }
  if (sign == RDIV_SIGN_ZERO) {
    *extra_error = ARITH_RDIV;
    code = PROJ_ERROR_UNSUPPORTED_ARITH_TERM;
    goto done;
  }

  init_rdiv_frac(out);
  out->num = arith_mul(p, lhs.num, rhs.den);
  out->den = arith_mul(p, lhs.den, rhs.num);
  ivector_add(&out->guards, lhs.guards.data, lhs.guards.size);
  ivector_add(&out->guards, rhs.guards.data, rhs.guards.size);
  if (guard != true_term) {
    ivector_push(&out->guards, guard);
  }

 done:
  delete_rdiv_frac(&lhs);
  delete_rdiv_frac(&rhs);
  return code;
}

static proj_flag_t fraction_of_arith(rdiv_preproc_t *p, term_t t, rdiv_frac_t *out, int32_t *extra_error) {
  term_kind_t kind;

  if (is_neg_term(t)) {
    *extra_error = ARITH_RDIV;
    return PROJ_ERROR_UNSUPPORTED_ARITH_TERM;
  }

  if (! is_arithmetic_term(p->terms, t)) {
    *extra_error = ARITH_RDIV;
    return PROJ_ERROR_UNSUPPORTED_ARITH_TERM;
  }

  kind = term_kind(p->terms, t);
  switch (kind) {
  case ARITH_CONSTANT:
  case UNINTERPRETED_TERM:
  case VARIABLE:
    frac_of_term(p, t, out);
    return PROJ_NO_ERROR;

  case ARITH_POLY:
    return fraction_of_poly(p, t, out, extra_error);

  case POWER_PRODUCT:
    return fraction_of_pprod(p, pprod_term_desc(p->terms, t), out, extra_error);

  case ARITH_RDIV:
    return fraction_of_rdiv(p, t, out, extra_error);

  default:
    *extra_error = ARITH_RDIV;
    return PROJ_ERROR_UNSUPPORTED_ARITH_TERM;
  }
}


/*
 * Atom/literal rewriting
 */

static proj_flag_t append_guard(rdiv_preproc_t *p, term_t guard, ivector_t *out, int32_t *extra_error) {
  if (guard == true_term) {
    return PROJ_NO_ERROR;
  }
  return rewrite_literal_rdiv(p, guard, out, extra_error);
}

static proj_flag_t append_guards(rdiv_preproc_t *p, const ivector_t *guards, ivector_t *out, int32_t *extra_error) {
  uint32_t i, n;
  proj_flag_t code;

  n = guards->size;
  for (i=0; i<n; i++) {
    code = append_guard(p, guards->data[i], out, extra_error);
    if (code != PROJ_NO_ERROR) {
      return code;
    }
  }
  return PROJ_NO_ERROR;
}

static term_t build_rewritten_atom(rdiv_preproc_t *p, rdiv_atom_kind_t kind, rdiv_sign_t den_sign, term_t num) {
  switch (kind) {
  case RDIV_ATOM_EQ:
    return mk_arith_term_eq0(p->mngr, num);

  case RDIV_ATOM_NEQ:
    return mk_arith_term_neq0(p->mngr, num);

  case RDIV_ATOM_GEQ:
    return den_sign == RDIV_SIGN_POS ? mk_arith_term_geq0(p->mngr, num) : mk_arith_term_leq0(p->mngr, num);

  case RDIV_ATOM_LT:
    return den_sign == RDIV_SIGN_POS ? mk_arith_term_lt0(p->mngr, num) : mk_arith_term_gt0(p->mngr, num);
  }

  assert(false);
  return NULL_TERM;
}

static proj_flag_t rewrite_arith_atom(rdiv_preproc_t *p, rdiv_atom_kind_t kind,
                                      term_t lhs, term_t rhs, term_t *atom,
                                      ivector_t *guards, int32_t *extra_error) {
  rdiv_frac_t lhs_frac, rhs_frac, diff;
  rdiv_sign_t sign;
  term_t guard;
  proj_flag_t code;

  code = fraction_of_arith(p, lhs, &lhs_frac, extra_error);
  if (code != PROJ_NO_ERROR) {
    return code;
  }

  code = fraction_of_arith(p, rhs, &rhs_frac, extra_error);
  if (code != PROJ_NO_ERROR) {
    delete_rdiv_frac(&lhs_frac);
    return code;
  }

  frac_sub(p, &lhs_frac, &rhs_frac, &diff);
  delete_rdiv_frac(&lhs_frac);
  delete_rdiv_frac(&rhs_frac);

  code = model_sign_and_guard(p, diff.den, &sign, &guard, extra_error);
  if (code != PROJ_NO_ERROR) {
    delete_rdiv_frac(&diff);
    return code;
  }
  if (sign == RDIV_SIGN_ZERO) {
    delete_rdiv_frac(&diff);
    *extra_error = ARITH_RDIV;
    return PROJ_ERROR_UNSUPPORTED_ARITH_TERM;
  }

  if (guard != true_term) {
    ivector_push(&diff.guards, guard);
  }
  *atom = build_rewritten_atom(p, kind, sign, diff.num);
  ivector_add(guards, diff.guards.data, diff.guards.size);

  delete_rdiv_frac(&diff);
  return PROJ_NO_ERROR;
}

static proj_flag_t rewrite_literal_rdiv(rdiv_preproc_t *p, term_t lit, ivector_t *out, int32_t *extra_error) {
  composite_term_t *d;
  ivector_t guards;
  term_kind_t kind;
  term_t base, atom;
  bool neg;
  proj_flag_t code;

  if (! term_contains_rdiv(p, lit)) {
    ivector_push(out, lit);
    return PROJ_NO_ERROR;
  }

  neg = is_neg_term(lit);
  base = unsigned_term(lit);
  kind = term_kind(p->terms, base);
  init_ivector(&guards, 0);

  switch (kind) {
  case ARITH_EQ_ATOM:
    code = rewrite_arith_atom(p, neg ? RDIV_ATOM_NEQ : RDIV_ATOM_EQ,
                              arith_eq_arg(p->terms, base), zero_term,
                              &atom, &guards, extra_error);
    break;

  case ARITH_GE_ATOM:
    code = rewrite_arith_atom(p, neg ? RDIV_ATOM_LT : RDIV_ATOM_GEQ,
                              arith_ge_arg(p->terms, base), zero_term,
                              &atom, &guards, extra_error);
    break;

  case ARITH_BINEQ_ATOM:
    d = arith_bineq_atom_desc(p->terms, base);
    assert(d->arity == 2);
    code = rewrite_arith_atom(p, neg ? RDIV_ATOM_NEQ : RDIV_ATOM_EQ,
                              d->arg[0], d->arg[1],
                              &atom, &guards, extra_error);
    break;

  default:
    *extra_error = ARITH_RDIV;
    code = PROJ_ERROR_UNSUPPORTED_ARITH_TERM;
    break;
  }

  if (code == PROJ_NO_ERROR) {
    if (atom != true_term) {
      ivector_push(out, atom);
    }
    code = append_guards(p, &guards, out, extra_error);
  }

  delete_ivector(&guards);
  return code;
}

proj_flag_t preprocess_rdiv_literals(rdiv_preprocess_cache_t *pre, uint32_t n, const term_t *a,
                                     ivector_t *v, int32_t *extra_error) {
  proj_flag_t code;
  ivector_t rewritten;
  uint32_t i;

  code = PROJ_NO_ERROR;
  init_ivector(&rewritten, 4);
  for (i=0; i<n; i++) {
    if (! cached_rdiv_rewrite(pre, a[i], v, extra_error, &code)) {
      ivector_reset(&rewritten);
      code = rewrite_literal_rdiv(pre, a[i], &rewritten, extra_error);
      cache_rdiv_rewrite(pre, a[i], code, *extra_error, &rewritten);
      if (code == PROJ_NO_ERROR) {
        ivector_add(v, rewritten.data, rewritten.size);
      } else {
        break;
      }
    } else if (code != PROJ_NO_ERROR) {
      break;
    }
  }
  delete_ivector(&rewritten);

  return code;
}
