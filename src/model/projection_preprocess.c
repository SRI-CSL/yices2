/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
#include "terms/rationals.h"
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
  evaluator_t *eval;
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
static proj_flag_t model_sign_and_guard_for(model_t *mdl, term_manager_t *mngr, term_table_t *terms,
                                            evaluator_t *eval, term_t t,
                                            rdiv_sign_t *sign, term_t *guard, int32_t *extra_error);


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

  cache->eval = NULL;
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

static term_t arith_const_for(term_manager_t *mngr, const rational_t *q) {
  rational_t tmp;
  term_t t;

  q_init(&tmp);
  q_set(&tmp, q);
  t = mk_arith_constant(mngr, &tmp);
  q_clear(&tmp);

  return t;
}

static term_t arith_one_for(term_manager_t *mngr) {
  rational_t q;
  term_t t;

  q_init(&q);
  q_set_one(&q);
  t = mk_arith_constant(mngr, &q);
  q_clear(&q);

  return t;
}

static term_t arith_add_for(term_manager_t *mngr, term_table_t *terms, term_t a, term_t b) {
  rba_buffer_t *buffer;

  buffer = term_manager_get_arith_buffer(mngr);
  reset_rba_buffer(buffer);
  rba_buffer_add_term(buffer, terms, a);
  rba_buffer_add_term(buffer, terms, b);

  return mk_arith_term(mngr, buffer);
}

static term_t arith_sub_for(term_manager_t *mngr, term_table_t *terms, term_t a, term_t b) {
  rba_buffer_t *buffer;

  buffer = term_manager_get_arith_buffer(mngr);
  reset_rba_buffer(buffer);
  rba_buffer_add_term(buffer, terms, a);
  rba_buffer_sub_term(buffer, terms, b);

  return mk_arith_term(mngr, buffer);
}

static term_t arith_mul_for(term_manager_t *mngr, term_table_t *terms, term_t a, term_t b) {
  rba_buffer_t *buffer;

  buffer = term_manager_get_arith_buffer(mngr);
  reset_rba_buffer(buffer);
  rba_buffer_add_term(buffer, terms, a);
  rba_buffer_mul_term(buffer, terms, b);

  return mk_arith_term(mngr, buffer);
}

static term_t arith_mul_const_for(term_manager_t *mngr, term_table_t *terms, const rational_t *q, term_t a) {
  rational_t tmp;
  rba_buffer_t *buffer;
  term_t t;

  q_init(&tmp);
  q_set(&tmp, q);
  buffer = term_manager_get_arith_buffer(mngr);
  reset_rba_buffer(buffer);
  rba_buffer_add_const_times_term(buffer, terms, &tmp, a);
  t = mk_arith_term(mngr, buffer);
  q_clear(&tmp);

  return t;
}

static term_t arith_const(rdiv_preproc_t *p, const rational_t *q) {
  return arith_const_for(p->mngr, q);
}

static term_t arith_one(rdiv_preproc_t *p) {
  return arith_one_for(p->mngr);
}

static term_t arith_add(rdiv_preproc_t *p, term_t a, term_t b) {
  return arith_add_for(p->mngr, p->terms, a, b);
}

static term_t arith_sub(rdiv_preproc_t *p, term_t a, term_t b) {
  return arith_sub_for(p->mngr, p->terms, a, b);
}

static term_t arith_mul(rdiv_preproc_t *p, term_t a, term_t b) {
  return arith_mul_for(p->mngr, p->terms, a, b);
}

static term_t arith_mul_const(rdiv_preproc_t *p, const rational_t *q, term_t a) {
  return arith_mul_const_for(p->mngr, p->terms, q, a);
}


/*
 * Exact ABS normalization
 */

typedef struct abs_rewriter_s {
  term_manager_t *mngr;
  term_table_t *terms;
  int_hmap_t cache;
} abs_rewriter_t;

static term_t rewrite_abs_term(abs_rewriter_t *rw, term_t t);

static term_t *rewrite_abs_children(abs_rewriter_t *rw, composite_term_t *d, bool *ok) {
  term_t *a;
  uint32_t i, n;

  n = d->arity;
  a = (term_t *) safe_malloc(n * sizeof(term_t));
  for (i=0; i<n; i++) {
    a[i] = rewrite_abs_term(rw, d->arg[i]);
    if (a[i] == NULL_TERM) {
      safe_free(a);
      *ok = false;
      return NULL;
    }
  }
  return a;
}

static term_t rewrite_abs_pprod(abs_rewriter_t *rw, pprod_t *p) {
  term_t *a;
  term_t r;
  uint32_t i, n;

  if (p == empty_pp || has_int_tag(p)) {
    return pprod_term(rw->terms, p);
  }

  n = p->len;
  a = (term_t *) safe_malloc(n * sizeof(term_t));
  for (i=0; i<n; i++) {
    a[i] = rewrite_abs_term(rw, p->prod[i].var);
    if (a[i] == NULL_TERM) {
      safe_free(a);
      return NULL_TERM;
    }
  }

  r = mk_pprod(rw->mngr, p, n, a);
  safe_free(a);
  return r;
}

static term_t rewrite_abs_poly(abs_rewriter_t *rw, polynomial_t *p) {
  term_t *a;
  term_t r;
  uint32_t i, n;

  n = p->nterms;
  a = (term_t *) safe_malloc(n * sizeof(term_t));
  for (i=0; i<n; i++) {
    if (p->mono[i].var == const_idx) {
      a[i] = const_idx;
    } else {
      a[i] = rewrite_abs_term(rw, p->mono[i].var);
      if (a[i] == NULL_TERM) {
        safe_free(a);
        return NULL_TERM;
      }
    }
  }

  r = mk_arith_poly(rw->mngr, p, n, a);
  safe_free(a);
  return r;
}

static term_t rewrite_abs_term(abs_rewriter_t *rw, term_t t) {
  int_hmap_pair_t *entry;
  composite_term_t *d;
  term_kind_t kind;
  term_t base, result, child, neg_child, cond, *a;
  type_t tau;
  bool neg, ok;

  if (t < 0) {
    return t;
  }

  entry = int_hmap_find(&rw->cache, t);
  if (entry != NULL) {
    return entry->val;
  }

  base = unsigned_term(t);
  neg = is_neg_term(t);
  kind = term_kind(rw->terms, base);
  result = base;

  switch (kind) {
  case ARITH_ABS:
    child = rewrite_abs_term(rw, arith_abs_arg(rw->terms, base));
    if (child != NULL_TERM) {
      cond = mk_arith_term_geq0(rw->mngr, child);
      neg_child = arith_sub_for(rw->mngr, rw->terms, zero_term, child);
      if (cond != NULL_TERM && neg_child != NULL_TERM) {
        tau = term_type(rw->terms, base);
        result = mk_ite(rw->mngr, cond, child, neg_child, tau);
        if (result == NULL_TERM) {
          result = base;
        }
      }
    }
    break;

  case ARITH_EQ_ATOM:
    child = rewrite_abs_term(rw, arith_eq_arg(rw->terms, base));
    if (child != NULL_TERM && child != arith_eq_arg(rw->terms, base)) {
      result = mk_arith_term_eq0(rw->mngr, child);
    }
    break;

  case ARITH_GE_ATOM:
    child = rewrite_abs_term(rw, arith_ge_arg(rw->terms, base));
    if (child != NULL_TERM && child != arith_ge_arg(rw->terms, base)) {
      result = mk_arith_term_geq0(rw->mngr, child);
    }
    break;

  case ARITH_IS_INT_ATOM:
    child = rewrite_abs_term(rw, arith_is_int_arg(rw->terms, base));
    if (child != NULL_TERM && child != arith_is_int_arg(rw->terms, base)) {
      result = mk_arith_is_int(rw->mngr, child);
    }
    break;

  case ARITH_FLOOR:
    child = rewrite_abs_term(rw, arith_floor_arg(rw->terms, base));
    if (child != NULL_TERM && child != arith_floor_arg(rw->terms, base)) {
      result = mk_arith_floor(rw->mngr, child);
    }
    break;

  case ARITH_CEIL:
    child = rewrite_abs_term(rw, arith_ceil_arg(rw->terms, base));
    if (child != NULL_TERM && child != arith_ceil_arg(rw->terms, base)) {
      result = mk_arith_ceil(rw->mngr, child);
    }
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
    d = ite_term_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_ite(rw->mngr, a[0], a[1], a[2], term_type(rw->terms, base));
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case APP_TERM:
    d = app_term_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_application(rw->mngr, a[0], d->arity - 1, a + 1);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case UPDATE_TERM:
    d = update_term_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_update(rw->mngr, a[0], d->arity - 2, a + 1, a[d->arity - 1]);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case TUPLE_TERM:
    d = tuple_term_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_tuple(rw->mngr, d->arity, a);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case SELECT_TERM:
    child = rewrite_abs_term(rw, select_term_arg(rw->terms, base));
    if (child != NULL_TERM && child != select_term_arg(rw->terms, base)) {
      result = mk_select(rw->mngr, select_term_index(rw->terms, base), child);
      if (result == NULL_TERM) {
        result = base;
      }
    }
    break;

  case BIT_TERM:
    child = rewrite_abs_term(rw, bit_term_arg(rw->terms, base));
    if (child != NULL_TERM && child != bit_term_arg(rw->terms, base)) {
      result = mk_bitextract(rw->mngr, child, bit_term_index(rw->terms, base));
      if (result == NULL_TERM) {
        result = base;
      }
    }
    break;

  case EQ_TERM:
    d = eq_term_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_eq(rw->mngr, a[0], a[1]);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case DISTINCT_TERM:
    d = distinct_term_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_distinct(rw->mngr, d->arity, a);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case OR_TERM:
    d = or_term_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_or_safe(rw->mngr, d->arity, a);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case XOR_TERM:
    d = xor_term_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_xor_safe(rw->mngr, d->arity, a);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case ARITH_BINEQ_ATOM:
    d = arith_bineq_atom_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_arith_eq(rw->mngr, a[0], a[1]);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case ARITH_RDIV:
    d = arith_rdiv_term_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_arith_rdiv(rw->mngr, a[0], a[1]);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case ARITH_IDIV:
    d = arith_idiv_term_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_arith_idiv(rw->mngr, a[0], a[1]);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case ARITH_MOD:
    d = arith_mod_term_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_arith_mod(rw->mngr, a[0], a[1]);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case ARITH_DIVIDES_ATOM:
    d = arith_divides_atom_desc(rw->terms, base);
    ok = true;
    a = rewrite_abs_children(rw, d, &ok);
    if (ok) {
      result = mk_arith_divides(rw->mngr, a[0], a[1]);
      if (result == NULL_TERM) {
        result = base;
      }
      safe_free(a);
    }
    break;

  case POWER_PRODUCT:
    result = rewrite_abs_pprod(rw, pprod_term_desc(rw->terms, base));
    if (result == NULL_TERM) {
      result = base;
    }
    break;

  case ARITH_POLY:
    result = rewrite_abs_poly(rw, poly_term_desc(rw->terms, base));
    if (result == NULL_TERM) {
      result = base;
    }
    break;

  default:
    result = base;
    break;
  }

  if (neg && result != base) {
    result = opposite_term(result);
  } else if (neg) {
    result = t;
  }

  int_hmap_add(&rw->cache, t, result);
  return result;
}

proj_flag_t preprocess_abs_terms(term_manager_t *mngr, uint32_t n, const term_t *a,
                                 ivector_t *v, int32_t *extra_error) {
  abs_rewriter_t rw;
  term_t t;
  uint32_t i;

  (void) extra_error;

  rw.mngr = mngr;
  rw.terms = mngr->terms;
  init_int_hmap(&rw.cache, 0);

  for (i=0; i<n; i++) {
    t = rewrite_abs_term(&rw, a[i]);
    ivector_push(v, t == NULL_TERM ? a[i] : t);
  }

  delete_int_hmap(&rw.cache);
  return PROJ_NO_ERROR;
}


/*
 * Cached per-cube elimination of floor/ceil/idiv/mod
 */

typedef struct arith_construct_cache_entry_s {
  ivector_t lits;
  ivector_t fresh_elims;
} arith_construct_cache_entry_t;

struct arith_construct_preprocess_cache_s {
  model_t *mdl;
  term_manager_t *mngr;
  term_table_t *terms;
  evaluator_t *eval;
  int_hmap_t map;
  arith_construct_cache_entry_t *data;
  uint32_t size;
  uint32_t capacity;
  ivector_t fresh_terms;
};

typedef arith_construct_preprocess_cache_t construct_preproc_t;

static void ivector_push_term_unique(ivector_t *v, term_t t) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    if (v->data[i] == t) {
      return;
    }
  }
  ivector_push(v, t);
}

static void ivector_add_terms_unique(ivector_t *v, const term_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    ivector_push_term_unique(v, a[i]);
  }
}

static void extend_arith_construct_cache(arith_construct_preprocess_cache_t *cache) {
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
  cache->data = (arith_construct_cache_entry_t *) safe_realloc(cache->data, n * sizeof(arith_construct_cache_entry_t));
  cache->capacity = n;
}

arith_construct_preprocess_cache_t *new_arith_construct_preprocess_cache(model_t *mdl, term_manager_t *mngr) {
  arith_construct_preprocess_cache_t *cache;

  cache = (arith_construct_preprocess_cache_t *) safe_malloc(sizeof(arith_construct_preprocess_cache_t));
  cache->mdl = mdl;
  cache->mngr = mngr;
  cache->terms = mngr->terms;
  assert(cache->terms == mdl->terms);

  cache->eval = NULL;
  init_int_hmap(&cache->map, 0);
  cache->data = NULL;
  cache->size = 0;
  cache->capacity = 0;
  init_ivector(&cache->fresh_terms, 0);

  return cache;
}

void delete_arith_construct_preprocess_cache(arith_construct_preprocess_cache_t *cache) {
  int_hmap_pair_t *r;
  uint32_t i, n;

  n = cache->size;
  for (i=0; i<n; i++) {
    delete_ivector(&cache->data[i].fresh_elims);
    delete_ivector(&cache->data[i].lits);
  }
  safe_free(cache->data);

  n = cache->fresh_terms.size;
  for (i=0; i<n; i++) {
    r = int_hmap_find(&cache->mdl->map, cache->fresh_terms.data[i]);
    if (r != NULL) {
      int_hmap_erase(&cache->mdl->map, r);
    }
  }
  delete_ivector(&cache->fresh_terms);

  delete_int_hmap(&cache->map);
  safe_free(cache);
}

static bool cached_arith_construct_rewrite(arith_construct_preprocess_cache_t *cache, term_t lit,
                                           ivector_t *out, ivector_t *fresh_elims) {
  int_hmap_pair_t *p;
  arith_construct_cache_entry_t *entry;

  p = int_hmap_find(&cache->map, lit);
  if (p == NULL) {
    return false;
  }

  assert(0 <= p->val && p->val < (int32_t) cache->size);
  entry = cache->data + p->val;
  ivector_add(out, entry->lits.data, entry->lits.size);
  ivector_add_terms_unique(fresh_elims, entry->fresh_elims.data, entry->fresh_elims.size);
  return true;
}

static void cache_arith_construct_rewrite(arith_construct_preprocess_cache_t *cache, term_t lit,
                                          const ivector_t *lits, const ivector_t *fresh_elims) {
  arith_construct_cache_entry_t *entry;
  uint32_t k;

  if (cache->size == cache->capacity) {
    extend_arith_construct_cache(cache);
  }

  k = cache->size;
  assert(k < (uint32_t) INT32_MAX);
  cache->size = k + 1;

  entry = cache->data + k;
  init_ivector(&entry->lits, lits->size);
  ivector_add(&entry->lits, lits->data, lits->size);
  init_ivector(&entry->fresh_elims, fresh_elims->size);
  ivector_add(&entry->fresh_elims, fresh_elims->data, fresh_elims->size);

  int_hmap_add(&cache->map, lit, (int32_t) k);
}

static bool eval_rational_value(construct_preproc_t *p, term_t t, rational_t *q) {
  value_t v;

  if (t == NULL_TERM) {
    return false;
  }

  if (term_kind(p->terms, t) == ARITH_CONSTANT) {
    q_set(q, rational_term_desc(p->terms, t));
    return true;
  }

  assert(p->eval != NULL);
  v = eval_in_model(p->eval, t);
  if (v < 0 || ! object_is_rational(&p->mdl->vtbl, v)) {
    return false;
  }

  q_set(q, vtbl_rational(&p->mdl->vtbl, v));
  return true;
}

static term_t fresh_int_aux(construct_preproc_t *p, const rational_t *value) {
  rational_t tmp;
  value_t v;
  term_t aux;

  assert(q_is_integer(value));

  // Yices terms are append-only: deleting this cache later removes only the
  // temporary model mapping, not the fresh term itself.
  aux = new_uninterpreted_term(p->terms, int_type(p->terms->types));
  if (aux == NULL_TERM) {
    return NULL_TERM;
  }

  q_init(&tmp);
  q_set(&tmp, value);
  v = vtbl_mk_rational(&p->mdl->vtbl, &tmp);
  q_clear(&tmp);

  model_map_term(p->mdl, aux, v);
  ivector_push(&p->fresh_terms, aux);
  return aux;
}

static void append_nontrue_literal(ivector_t *v, term_t lit) {
  if (lit != true_term) {
    ivector_push(v, lit);
  }
}

static bool term_contains_arith_construct(construct_preproc_t *p, term_t t);

static bool pprod_contains_arith_construct(construct_preproc_t *p, pprod_t *prod) {
  uint32_t i, n;

  if (pp_is_empty(prod)) {
    return false;
  }
  if (pp_is_var(prod)) {
    return term_contains_arith_construct(p, var_of_pp(prod));
  }

  n = prod->len;
  for (i=0; i<n; i++) {
    if (term_contains_arith_construct(p, prod->prod[i].var)) {
      return true;
    }
  }
  return false;
}

static bool term_contains_arith_construct(construct_preproc_t *p, term_t t) {
  composite_term_t *d;
  polynomial_t *poly;
  term_kind_t kind;
  uint32_t i, n;

  t = unsigned_term(t);
  kind = term_kind(p->terms, t);

  switch (kind) {
  case ARITH_FLOOR:
  case ARITH_CEIL:
  case ARITH_IDIV:
  case ARITH_MOD:
    return true;

  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
  case ARITH_IS_INT_ATOM:
  case ARITH_ABS:
    return term_contains_arith_construct(p, unary_term_arg(p->terms, t));

  case ARITH_POLY:
    poly = poly_term_desc(p->terms, t);
    n = poly->nterms;
    for (i=0; i<n; i++) {
      if (poly->mono[i].var != const_idx &&
          term_contains_arith_construct(p, poly->mono[i].var)) {
        return true;
      }
    }
    return false;

  case POWER_PRODUCT:
    return pprod_contains_arith_construct(p, pprod_term_desc(p->terms, t));

  case SELECT_TERM:
    return term_contains_arith_construct(p, select_term_arg(p->terms, t));

  case BIT_TERM:
    return term_contains_arith_construct(p, bit_term_arg(p->terms, t));

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
  case ARITH_RDIV:
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
      if (term_contains_arith_construct(p, d->arg[i])) {
        return true;
      }
    }
    return false;

  default:
    return false;
  }
}

static bool rewrite_construct_arith(construct_preproc_t *p, term_t t, term_t *out,
                                    ivector_t *guards, ivector_t *fresh_elims);

static bool rewrite_construct_pprod(construct_preproc_t *p, pprod_t *prod, term_t *out,
                                    ivector_t *guards, ivector_t *fresh_elims) {
  term_t *a;
  term_t r;
  uint32_t i, n;

  if (prod == empty_pp || has_int_tag(prod)) {
    *out = pprod_term(p->terms, prod);
    return true;
  }

  n = prod->len;
  a = (term_t *) safe_malloc(n * sizeof(term_t));
  for (i=0; i<n; i++) {
    if (! rewrite_construct_arith(p, prod->prod[i].var, a+i, guards, fresh_elims)) {
      safe_free(a);
      return false;
    }
  }

  r = mk_pprod(p->mngr, prod, n, a);
  safe_free(a);
  if (r == NULL_TERM) {
    return false;
  }
  *out = r;
  return true;
}

static bool rewrite_construct_poly(construct_preproc_t *p, polynomial_t *poly, term_t *out,
                                   ivector_t *guards, ivector_t *fresh_elims) {
  term_t *a;
  term_t r;
  uint32_t i, n;

  n = poly->nterms;
  a = (term_t *) safe_malloc(n * sizeof(term_t));
  for (i=0; i<n; i++) {
    if (poly->mono[i].var == const_idx) {
      a[i] = const_idx;
    } else if (! rewrite_construct_arith(p, poly->mono[i].var, a+i, guards, fresh_elims)) {
      safe_free(a);
      return false;
    }
  }

  r = mk_arith_poly(p->mngr, poly, n, a);
  safe_free(a);
  if (r == NULL_TERM) {
    return false;
  }
  *out = r;
  return true;
}

static bool rewrite_construct_children2(construct_preproc_t *p, composite_term_t *d,
                                        term_t *a, term_t *b,
                                        ivector_t *guards, ivector_t *fresh_elims) {
  assert(d->arity == 2);
  return rewrite_construct_arith(p, d->arg[0], a, guards, fresh_elims) &&
         rewrite_construct_arith(p, d->arg[1], b, guards, fresh_elims);
}

static bool append_floor_guards(construct_preproc_t *p, term_t aux, term_t arg,
                                bool is_floor, ivector_t *guards) {
  term_t one, bound, g1, g2;

  one = arith_one_for(p->mngr);
  if (is_floor) {
    bound = arith_add_for(p->mngr, p->terms, aux, one);
    if (bound == NULL_TERM) {
      return false;
    }
    g1 = mk_arith_leq(p->mngr, aux, arg);   // aux <= arg
    g2 = mk_arith_lt(p->mngr, arg, bound);  // arg < aux + 1
  } else {
    bound = arith_sub_for(p->mngr, p->terms, aux, one);
    if (bound == NULL_TERM) {
      return false;
    }
    g1 = mk_arith_leq(p->mngr, arg, aux);   // arg <= aux
    g2 = mk_arith_lt(p->mngr, bound, arg);  // aux - 1 < arg
  }

  if (g1 == NULL_TERM || g2 == NULL_TERM) {
    return false;
  }
  append_nontrue_literal(guards, g1);
  append_nontrue_literal(guards, g2);
  return true;
}

static bool rewrite_floor_or_ceil(construct_preproc_t *p, term_t arg, bool is_floor,
                                  term_t *out, ivector_t *guards, ivector_t *fresh_elims) {
  rational_t value;
  term_t rewritten_arg, aux, floor_term;
  bool ok;

  if (! rewrite_construct_arith(p, arg, &rewritten_arg, guards, fresh_elims)) {
    return false;
  }

  q_init(&value);
  floor_term = is_floor ? mk_arith_floor(p->mngr, rewritten_arg)
                        : mk_arith_ceil(p->mngr, rewritten_arg);
  ok = eval_rational_value(p, floor_term, &value);
  if (! ok || ! q_is_integer(&value)) {
    q_clear(&value);
    return false;
  }

  aux = fresh_int_aux(p, &value);
  q_clear(&value);
  if (aux == NULL_TERM) {
    return false;
  }

  if (! append_floor_guards(p, aux, rewritten_arg, is_floor, guards)) {
    return false;
  }
  ivector_push_term_unique(fresh_elims, aux);
  *out = aux;
  return true;
}

static bool append_division_cell_guards(construct_preproc_t *p, term_t lhs, term_t rhs,
                                        term_t aux, rdiv_sign_t sign, term_t sign_guard,
                                        ivector_t *guards) {
  term_t one, q_bound, q_times_rhs, bound_times_rhs, g1, g2;

  assert(sign == RDIV_SIGN_POS || sign == RDIV_SIGN_NEG);

  if (sign_guard != true_term) {
    ivector_push(guards, sign_guard);
  }

  one = arith_one_for(p->mngr);
  q_bound = sign == RDIV_SIGN_POS ? arith_add_for(p->mngr, p->terms, aux, one)
                                  : arith_sub_for(p->mngr, p->terms, aux, one);
  if (q_bound == NULL_TERM) {
    return false;
  }
  q_times_rhs = arith_mul_for(p->mngr, p->terms, aux, rhs);
  bound_times_rhs = arith_mul_for(p->mngr, p->terms, q_bound, rhs);
  if (q_times_rhs == NULL_TERM || bound_times_rhs == NULL_TERM) {
    return false;
  }
  g1 = mk_arith_leq(p->mngr, q_times_rhs, lhs);
  g2 = mk_arith_lt(p->mngr, lhs, bound_times_rhs);
  if (g1 == NULL_TERM || g2 == NULL_TERM) {
    return false;
  }

  append_nontrue_literal(guards, g1);
  append_nontrue_literal(guards, g2);
  return true;
}

static bool quotient_model_value(construct_preproc_t *p, term_t lhs, term_t rhs,
                                 rational_t *quotient, rdiv_sign_t *sign, term_t *sign_guard) {
  int32_t extra_error;
  term_t div;
  proj_flag_t code;

  extra_error = 0;
  assert(p->eval != NULL);
  code = model_sign_and_guard_for(p->mdl, p->mngr, p->terms, p->eval, rhs, sign, sign_guard, &extra_error);
  if (code != PROJ_NO_ERROR || *sign == RDIV_SIGN_ZERO) {
    return false;
  }

  div = mk_arith_idiv(p->mngr, lhs, rhs);
  if (div == NULL_TERM || ! eval_rational_value(p, div, quotient) || ! q_is_integer(quotient)) {
    return false;
  }
  return true;
}

static bool rewrite_idiv_or_mod(construct_preproc_t *p, term_t lhs, term_t rhs, bool is_mod,
                                term_t *out, ivector_t *guards, ivector_t *fresh_elims) {
  rational_t quotient;
  term_t lhs_rewritten, rhs_rewritten, aux, sign_guard, product;
  rdiv_sign_t sign;
  bool ok;

  if (! rewrite_construct_arith(p, lhs, &lhs_rewritten, guards, fresh_elims) ||
      ! rewrite_construct_arith(p, rhs, &rhs_rewritten, guards, fresh_elims)) {
    return false;
  }

  q_init(&quotient);
  ok = quotient_model_value(p, lhs_rewritten, rhs_rewritten, &quotient, &sign, &sign_guard);
  if (! ok) {
    q_clear(&quotient);
    return false;
  }

  aux = fresh_int_aux(p, &quotient);
  q_clear(&quotient);
  if (aux == NULL_TERM) {
    return false;
  }

  if (! append_division_cell_guards(p, lhs_rewritten, rhs_rewritten, aux, sign, sign_guard, guards)) {
    return false;
  }

  ivector_push_term_unique(fresh_elims, aux);
  if (is_mod) {
    product = arith_mul_for(p->mngr, p->terms, rhs_rewritten, aux);
    if (product == NULL_TERM) {
      return false;
    }
    *out = arith_sub_for(p->mngr, p->terms, lhs_rewritten, product);
    return *out != NULL_TERM;
  }

  *out = aux;
  return true;
}

static bool rewrite_construct_arith(construct_preproc_t *p, term_t t, term_t *out,
                                    ivector_t *guards, ivector_t *fresh_elims) {
  composite_term_t *d;
  term_kind_t kind;
  term_t a, b, r;

  if (is_neg_term(t) || ! is_arithmetic_term(p->terms, t)) {
    return false;
  }

  kind = term_kind(p->terms, t);
  switch (kind) {
  case ARITH_CONSTANT:
  case UNINTERPRETED_TERM:
  case VARIABLE:
    *out = t;
    return true;

  case ARITH_POLY:
    return rewrite_construct_poly(p, poly_term_desc(p->terms, t), out, guards, fresh_elims);

  case POWER_PRODUCT:
    return rewrite_construct_pprod(p, pprod_term_desc(p->terms, t), out, guards, fresh_elims);

  case ARITH_FLOOR:
    return rewrite_floor_or_ceil(p, arith_floor_arg(p->terms, t), true, out, guards, fresh_elims);

  case ARITH_CEIL:
    return rewrite_floor_or_ceil(p, arith_ceil_arg(p->terms, t), false, out, guards, fresh_elims);

  case ARITH_IDIV:
    d = arith_idiv_term_desc(p->terms, t);
    return rewrite_idiv_or_mod(p, d->arg[0], d->arg[1], false, out, guards, fresh_elims);

  case ARITH_MOD:
    d = arith_mod_term_desc(p->terms, t);
    return rewrite_idiv_or_mod(p, d->arg[0], d->arg[1], true, out, guards, fresh_elims);

  case ARITH_RDIV:
    d = arith_rdiv_term_desc(p->terms, t);
    if (! rewrite_construct_children2(p, d, &a, &b, guards, fresh_elims)) {
      return false;
    }
    r = mk_arith_rdiv(p->mngr, a, b);
    if (r == NULL_TERM) {
      return false;
    }
    *out = r;
    return true;

  default:
    if (term_contains_arith_construct(p, t)) {
      return false;
    }
    *out = t;
    return true;
  }
}

static bool rewrite_literal_arith_construct(construct_preproc_t *p, term_t lit,
                                            ivector_t *out, ivector_t *fresh_elims) {
  composite_term_t *d;
  ivector_t guards;
  term_kind_t kind;
  term_t base, atom, a, b;
  bool neg, ok;
  uint32_t fresh_start;

  if (! term_contains_arith_construct(p, lit)) {
    ivector_push(out, lit);
    return true;
  }

  neg = is_neg_term(lit);
  base = unsigned_term(lit);
  kind = term_kind(p->terms, base);
  init_ivector(&guards, 0);
  fresh_start = fresh_elims->size;
  ok = false;
  atom = lit;

  switch (kind) {
  case ARITH_EQ_ATOM:
    ok = rewrite_construct_arith(p, arith_eq_arg(p->terms, base), &a, &guards, fresh_elims);
    if (ok) {
      atom = neg ? mk_arith_term_neq0(p->mngr, a) : mk_arith_term_eq0(p->mngr, a);
      ok = atom != NULL_TERM;
    }
    break;

  case ARITH_GE_ATOM:
    ok = rewrite_construct_arith(p, arith_ge_arg(p->terms, base), &a, &guards, fresh_elims);
    if (ok) {
      atom = neg ? mk_arith_term_lt0(p->mngr, a) : mk_arith_term_geq0(p->mngr, a);
      ok = atom != NULL_TERM;
    }
    break;

  case ARITH_BINEQ_ATOM:
    d = arith_bineq_atom_desc(p->terms, base);
    ok = rewrite_construct_children2(p, d, &a, &b, &guards, fresh_elims);
    if (ok) {
      atom = neg ? mk_arith_neq(p->mngr, a, b) : mk_arith_eq(p->mngr, a, b);
      ok = atom != NULL_TERM;
    }
    break;

  case ARITH_IS_INT_ATOM:
    ok = rewrite_construct_arith(p, arith_is_int_arg(p->terms, base), &a, &guards, fresh_elims);
    if (ok) {
      atom = mk_arith_is_int(p->mngr, a);
      if (neg && atom != NULL_TERM) {
        atom = opposite_term(atom);
      }
      ok = atom != NULL_TERM;
    }
    break;

  case ARITH_DIVIDES_ATOM:
    d = arith_divides_atom_desc(p->terms, base);
    ok = rewrite_construct_arith(p, d->arg[1], &b, &guards, fresh_elims);
    if (ok) {
      atom = mk_arith_divides(p->mngr, d->arg[0], b);
      if (neg && atom != NULL_TERM) {
        atom = opposite_term(atom);
      }
      ok = atom != NULL_TERM;
    }
    break;

  default:
    ok = false;
    break;
  }

  if (ok) {
    ivector_add(out, guards.data, guards.size);
    append_nontrue_literal(out, atom);
  } else {
    fresh_elims->size = fresh_start;
    ivector_push(out, lit);
  }

  delete_ivector(&guards);
  return true;
}

proj_flag_t preprocess_arith_construct_literals(arith_construct_preprocess_cache_t *pre,
                                                evaluator_t *eval,
                                                uint32_t n, const term_t *a,
                                                ivector_t *v, ivector_t *fresh_elims,
                                                int32_t *extra_error) {
  ivector_t rewritten, local_fresh;
  uint32_t i;

  (void) extra_error;
  assert(eval != NULL);
  assert(pre->eval == NULL);
  pre->eval = eval;

  init_ivector(&rewritten, 4);
  init_ivector(&local_fresh, 2);
  for (i=0; i<n; i++) {
    if (! cached_arith_construct_rewrite(pre, a[i], v, fresh_elims)) {
      ivector_reset(&rewritten);
      ivector_reset(&local_fresh);
      (void) rewrite_literal_arith_construct(pre, a[i], &rewritten, &local_fresh);
      cache_arith_construct_rewrite(pre, a[i], &rewritten, &local_fresh);
      ivector_add(v, rewritten.data, rewritten.size);
      ivector_add_terms_unique(fresh_elims, local_fresh.data, local_fresh.size);
    }
  }
  delete_ivector(&local_fresh);
  delete_ivector(&rewritten);
  pre->eval = NULL;

  return PROJ_NO_ERROR;
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

static proj_flag_t model_sign_and_guard_for(model_t *mdl, term_manager_t *mngr, term_table_t *terms,
                                            evaluator_t *eval, term_t t,
                                            rdiv_sign_t *sign, term_t *guard, int32_t *extra_error) {
  value_t v;
  int32_t sgn;

  assert(is_arithmetic_term(terms, t));

  if (term_kind(terms, t) == ARITH_CONSTANT) {
    sgn = q_sgn(rational_term_desc(terms, t));
  } else {
    v = eval_in_model(eval, t);
    if (v < 0) {
      *extra_error = v;
      return PROJ_ERROR_IN_EVAL;
    }

    if (object_is_rational(&mdl->vtbl, v)) {
      sgn = q_sgn(vtbl_rational(&mdl->vtbl, v));
    } else {
#ifdef HAVE_MCSAT
      assert(object_is_algebraic(&mdl->vtbl, v));
      sgn = lp_algebraic_number_sgn(vtbl_algebraic_number(&mdl->vtbl, v));
#else
      *extra_error = v;
      return PROJ_ERROR_IN_EVAL;
#endif
    }
  }

  // If t is nonlinear, the sign guard may also be nonlinear. That is
  // intentional: projection may skip this cube in non-MCSAT builds,
  // but the guarded rewrite remains sound for cubes that can project.
  if (sgn > 0) {
    *sign = RDIV_SIGN_POS;
    *guard = (term_kind(terms, t) == ARITH_CONSTANT) ? true_term : mk_arith_term_gt0(mngr, t);
  } else if (sgn < 0) {
    *sign = RDIV_SIGN_NEG;
    *guard = (term_kind(terms, t) == ARITH_CONSTANT) ? true_term : mk_arith_term_lt0(mngr, t);
  } else {
    *sign = RDIV_SIGN_ZERO;
    *guard = true_term;
  }

  return PROJ_NO_ERROR;
}

static proj_flag_t model_sign_and_guard(rdiv_preproc_t *p, term_t t, rdiv_sign_t *sign, term_t *guard, int32_t *extra_error) {
  assert(p->eval != NULL);
  return model_sign_and_guard_for(p->mdl, p->mngr, p->terms, p->eval, t, sign, guard, extra_error);
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

proj_flag_t preprocess_rdiv_literals(rdiv_preprocess_cache_t *pre, evaluator_t *eval,
                                     uint32_t n, const term_t *a,
                                     ivector_t *v, int32_t *extra_error) {
  proj_flag_t code;
  ivector_t rewritten;
  uint32_t i;

  assert(eval != NULL);
  assert(pre->eval == NULL);
  pre->eval = eval;
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
  pre->eval = NULL;

  return code;
}
