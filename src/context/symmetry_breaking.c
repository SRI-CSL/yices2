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
 * SUPPORT FOR BREAKING SYMMETRIES IN UF FORMULAS
 */

#include <stdbool.h>
#include <assert.h>

#include "context/context_utils.h"
#include "context/internalization_codes.h"
#include "context/symmetry_breaking.h"
#include "utils/int_array_sort.h"
#include "utils/memalloc.h"
#include "utils/ptr_array_sort2.h"

#define TRACE 0

#if TRACE
#include "io/term_printer.h"
#endif



/*
 * RANGE-CONSTRAINT RECORDS
 */

/*
 * Hash for a set of constants a[0 ... n-1]
 * - we use index_of(a[i]) since the sign bit of a[i] is 0
 */
static uint32_t hash_const_set(term_t *a, uint32_t n) {
  uint32_t h, i;

  h = 0;
  for (i=0; i<n; i++) {
    h |= ((uint32_t) 1) << ((uint32_t) index_of(a[i]) & 0x1f);
  }
  return h;
}


/*
 * Initialize r for the set of constants a[0 ... n-1]
 * - a must be sorted
 * - arrays r->trm/r->idx are allocated with default initial size
 */
static void init_rng_record(rng_record_t *r, term_t *a, uint32_t n) {
  term_t *tmp;
  uint32_t i, nt;

  assert(n <= UINT32_MAX/sizeof(term_t));

  tmp = (term_t *) safe_malloc(n * sizeof(term_t));
  for (i=0; i<n; i++) {
    tmp[i] = a[i];
  }

  nt = DEF_RNG_RECORD_SIZE;
  assert(nt <= MAX_RNG_RECORD_SIZE);

  r->cst = tmp;
  r->trm = (term_t *) safe_malloc(nt * sizeof(term_t));
  r->idx = (uint32_t *) safe_malloc(nt * sizeof(uint32_t));
  r->hash = hash_const_set(a, n);
  r->num_constants = n;
  r->num_terms = 0;
  r->size = nt;
}


/*
 * Make arrays trm and idx 50% larger
 */
static void extend_rng_record(rng_record_t *r) {
  uint32_t n;

  n = r->size;
  n += n >> 1;
  assert(n > r->size);

  if (n > MAX_RNG_RECORD_SIZE) {
    out_of_memory();
  }
  r->trm = (term_t *) safe_realloc(r->trm, n * sizeof(term_t));
  r->idx = (uint32_t *) safe_realloc(r->idx, n * sizeof(uint32_t));
  r->size = n;
}


/*
 * Add pair (t, id) to the record
 */
static void rng_record_add(rng_record_t *r, term_t t, uint32_t id) {
  uint32_t i;

  i = r->num_terms;
  if (i == r->size) {
    extend_rng_record(r);
  }
  assert(i < r->size);
  r->trm[i] = t;
  r->idx[i] = id;
  r->num_terms = i+1;
}


/*
 * Delete the whole thing
 */
static void delete_rng_record(rng_record_t *r) {
  safe_free(r->cst);
  safe_free(r->trm);
  safe_free(r->idx);
}


/*
 * Check whether r->cst is equal to a[0 ... n-1]
 * - a must be sorted
 */
static bool equal_arrays(term_t *a, term_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] != b[i]) {
      return false;
    }
  }

  return true;
}

static bool rng_record_match(rng_record_t *r, term_t *a, uint32_t n) {
  return r->num_constants == n && equal_arrays(r->cst, a, n);
}




/*
 * Check whether r1's constant set is strictly included in r2's constant set
 */
bool range_record_subset(rng_record_t *r1, rng_record_t *r2) {
  uint32_t i, j, n1, n2;
  term_t c;

  n1 = r1->num_constants;
  n2 = r2->num_constants;

  if ((r1->hash & ~r2->hash) == 0 && n1 < n2) {
    i = 0;
    j = 0;

    while (i < n1) {
      c = r1->cst[i];
      i ++;
      while (j < n2 && r2->cst[j] < c) j++;
      if (j == n2 || r2->cst[j] > c) goto not_subset;
      assert(r2->cst[j] == c);
      j ++;
    }

    return true;
  }

 not_subset:
  return false;
}



/*
 * ARRAY OF RANGE-CONSTRAINT RECORDS
 */

static void init_rng_vector(rng_vector_t *v) {
  v->data = NULL;
  v->nelems = 0;
  v->size = 0;
}

static void extend_rng_vector(rng_vector_t *v) {
  uint32_t n;

  n = v->size;
  if (n == 0) {
    /*
     *  initial allocation: use DEF_RNG_VECTOR_SIZE
     */
    n = DEF_RNG_VECTOR_SIZE;
    assert(v->data == NULL && n <= MAX_RNG_VECTOR_SIZE);

    v->data = (rng_record_t *) safe_malloc(n * sizeof(rng_record_t));
    v->size = n;
  } else {
    /*
     * Make it 50% larger
     */
    n += (n>>1) + 1;
    assert(n > v->size);

    if (n > MAX_RNG_VECTOR_SIZE) {
      out_of_memory();
    }

    v->data = (rng_record_t *) safe_realloc(v->data, n * sizeof(rng_record_t));
    v->size = n;
  }
}


static void delete_rng_vector(rng_vector_t *rng) {
  uint32_t i, n;

  n = rng->nelems;
  for (i=0; i<n; i++) {
    delete_rng_record(rng->data + i);
  }
  safe_free(rng->data);
  rng->data = NULL;
}



/*
 * Add a range constraint to v:
 * - a[0 ... n-1] = the constant for this constraint
 * - t = term, id = index
 * - a must be sorted.
 */
static void add_range_constraint(rng_vector_t *v, term_t *a, uint32_t n, term_t t, uint32_t id) {
  uint32_t i, p;

  p = v->nelems;
  for (i=0; i<p; i++) {
    if (rng_record_match(v->data + i, a, n)) {
      rng_record_add(v->data + i, t, id);
      return;
    }
  }

  // create a new record
  if (i == v->size) {
    extend_rng_vector(v);
  }
  assert(i < v->size);
  init_rng_record(v->data + i, a, n);
  rng_record_add(v->data + i, t, id);
  v->nelems = i+1;
}




/*
 * FORMULA PROCESSING
 */

/*
 * For breadth-first term exploration we use a queue + cache
 * - terms to be processed are in the queue
 * - terms already processed or already in the queue are in cache
 */

/*
 * Add t to queue and cache if it's not already in the cache
 */
static void push_term(int_queue_t *queue, int_hset_t *cache, term_t t) {
  if (int_hset_add(cache, t)) {
    int_queue_push(queue, t);
  }
}

/*
 * Add all children of composite c to the queue/cache
 */
static void push_children(int_queue_t *queue, int_hset_t *cache, composite_term_t *c) {
  uint32_t i, n;

  n = c->arity;
  for (i=0; i<n; i++) {
    push_term(queue, cache, c->arg[i]);
  }
}

/*
 * Add last child of c to the queue/cache (for lambda/forall)
 */
static void push_last_child(int_queue_t *queue, int_hset_t *cache, composite_term_t *c) {
  uint32_t n;

  n = c->arity;
  push_term(queue, cache, c->arg[n-1]);
}


/*
 * Polynomials and power products
 */
static void push_poly_vars(int_queue_t *queue, int_hset_t *cache, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  assert(n > 0);

  i = 0;
  if (p->mono[i].var == const_idx) { // skip constant
    i = 1;
  }
  while (i<n) {
    push_term(queue, cache, p->mono[i].var);
    i ++;
  }
}

static void push_bvpoly64_vars(int_queue_t *queue, int_hset_t *cache, bvpoly64_t *p) {
  uint32_t i, n;

  n = p->nterms;
  assert(n > 0);

  i = 0;
  if (p->mono[i].var == const_idx) { // skip constant
    i = 1;
  }
  while (i<n) {
    push_term(queue, cache, p->mono[i].var);
    i ++;
  }
}

static void push_bvpoly_vars(int_queue_t *queue, int_hset_t *cache, bvpoly_t *p) {
  uint32_t i, n;

  n = p->nterms;
  assert(n > 0);

  i = 0;
  if (p->mono[i].var == const_idx) { // skip constant
    i = 1;
  }
  while (i<n) {
    push_term(queue, cache, p->mono[i].var);
    i ++;
  }
}

static void push_pprod_vars(int_queue_t *queue, int_hset_t *cache, pprod_t *p) {
  uint32_t i, n;

  n = p->len;
  for (i=0; i<n; i++) {
    push_term(queue, cache, p->prod[i].var);
  }
}


/*
 * Check whether t is a constant
 * - t must have positive polarity
 */
static bool term_is_constant(term_table_t *table, term_t t) {
  term_kind_t kind;

  assert(is_pos_term(t));
  kind = term_kind(table, t);
  return kind == CONSTANT_TERM || kind == UNINTERPRETED_TERM;
}

static bool term_is_uconst(term_table_t *table, term_t t) {
  assert(is_pos_term(t));
  return term_kind(table, t) == UNINTERPRETED_TERM;
}


/*
 * Check for equality that trivially reduce to false
 */
static bool false_eq(term_table_t *table, term_t t1, term_t t2) {
  return t1 != t2 && term_kind(table, t1) == CONSTANT_TERM && term_kind(table, t2) == CONSTANT_TERM;
}

/*
 * Check whether t is of the following forms
 * - false term
 * - disjunction: (or t1 ... tn)
 * - equality (x == constant) or (constant == x)
 * - boolean equivalence: (x == true) or (x == false)
 *
 * The function returns one of the following codes:
 * - MATCH_FALSE
 * - MATCH_OR
 * - MATCH_EQ
 * - MATCH_IFF
 * - MATCH_OTHER
 *
 * In case of MATCH_EQ it stores the constant in *a and the other
 * term in *x. Warning: *x may be uninterpreted.
 *
 * In case of MATCH_IFF: the function stores a Boolean term *x
 * such that x is equivalent to t.
 */
typedef enum match_code {
  MATCH_FALSE,
  MATCH_OR,
  MATCH_EQ,
  MATCH_IFF,
  MATCH_OTHER,
} match_code_t;

static match_code_t match_term(context_t *ctx, term_t t, term_t *a, term_t *x) {
  composite_term_t *eq;
  term_table_t *terms;
  match_code_t code;
  term_t t1, t2;

  if (term_is_false(ctx, t)) {
    code = MATCH_FALSE;
  } else {
    code = MATCH_OTHER;
    terms = ctx->terms;

    switch (term_kind(terms, t)) {
    case OR_TERM:
      if (is_pos_term(t)) {
	code = MATCH_OR;
      }
      break;

    case EQ_TERM:
      eq = eq_term_desc(terms, t);
      t1 = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
      t2 = intern_tbl_get_root(&ctx->intern, eq->arg[1]);
      if (is_boolean_term(terms, t1)) {
	assert(is_boolean_term(terms, t2));
	/*
	 * t is either (iff t1 t2) or (not (iff t1 t2))
	 * we rewrite (not (iff t1 t2)) to (iff t1 (not t2))
	 */
	if (is_neg_term(t)) {
	  t2 = opposite_term(t2);
	}
	/*
	 * Check whether t1 or t2 is true or false
	 */
	if (term_is_true(ctx, t1)) {
	  code = MATCH_IFF;
	  *x = t2;
	} else if (term_is_false(ctx, t1)) {
	  code = MATCH_IFF;
	  *x = opposite_term(t2);
	} else if (term_is_true(ctx, t2)) {
	  code = MATCH_IFF;
	  *x = t1;
	} else if (term_is_false(ctx, t2)) {
	  code = MATCH_IFF;
	  *x = opposite_term(t1);
	}

      } else if (is_pos_term(t) && t1 != t2) {
	/*
	 * t is (eq t1 t2)
	 * t1 and t2 are not Boolean
	 * if t1 and t2 are equal, we return MATCH_OTHER, since (eq t1 t2) is true
	 */
	assert(is_pos_term(t1) && is_pos_term(t2));
	if (false_eq(terms, t1, t2)) {
	  code = MATCH_FALSE;
	} else if (term_is_constant(terms, t1)) {
	  *a = t1;
	  *x = t2;
	  code = MATCH_EQ;
	} else if (term_is_constant(terms, t2)) {
	  *a = t2;
	  *x = t1;
	  code = MATCH_EQ;
	}

      } else if (is_neg_term(t) && t1 == t2) {
	/*
	 * t is (not (eq t1 t2))
	 * t1 and t2 are equal so t matches false.
	 */
	code = MATCH_FALSE;
      }
      break;

    default:
      break;
    }
  }

  return code;
}


/*
 * Check whether f is a range constraint
 * - if so return a term t and fill in vector v with the formula's constants
 * - otherwise, return NULL_TERM
 *
 * Side effect: use queue and cache.
 * v may be modified even if the function returns NULL_TERM.
 */
static term_t formula_is_range_constraint(sym_breaker_t *breaker, term_t f, ivector_t *v) {
  int_queue_t *queue;
  int_hset_t *cache;
  term_table_t *terms;
  intern_tbl_t *intern;
  term_t r, t;
  term_t x, a, y, b;
  uint32_t neqs;

  queue = &breaker->queue;
  cache = &breaker->cache;
  terms = breaker->terms;
  intern = &breaker->ctx->intern;

  assert(int_queue_is_empty(queue) && int_hset_is_empty(cache));
  push_term(queue, cache, f);

  neqs = 0;
  t = NULL_TERM;

  y = NULL_TERM; // prevent GCC warning
  b = NULL_TERM; // prevent GCC warning

  /*
   * Invariants:
   * - neqs = number of equality atoms seen so far
   * - if neq == 1, then the first equality is stored as (y == b) where b is a constant
   * - if neq >= 2, then all equalities seen so far were of the form (y == constant)
   */
  do {
    // r := root of the first term in the queue
    r = intern_tbl_get_root(intern, int_queue_pop(queue));

    switch (match_term(breaker->ctx, r, &a, &x)) {
    case MATCH_FALSE: // skip false terms
      break;

    case MATCH_OR:
      push_children(queue, cache, or_term_desc(terms, r));
      break;

    case MATCH_EQ:
      assert(term_is_constant(terms, a));
      if (neqs == 0) {
	y = x; b = a;
      } else if (neqs == 1) {
	/*
	 * First equality: (y == b). Second equality: (x == a)
	 */
	if (y == x) {
	  // y is the common term, a and b are constant
	  ivector_push(v, b);
	  ivector_push(v, a);
	} else if (y == a && term_is_uconst(terms, x)) {
	  // y is the common term, b and x are constant
	  ivector_push(v, b);
	  ivector_push(v, a);
	} else if (x == b && term_is_uconst(terms, y)) {
	  // b is the common term, y and a are constant
	  ivector_push(v, y);
	  ivector_push(v, a);
	  y = b;
	} else if (a == b && term_is_uconst(terms, y) && term_is_uconst(terms, x)) {
	  // b is the common term, y and x are constant
	  ivector_push(v, y);
	  ivector_push(v, x);
	  y = b;
	} else {
	  // abort
	  goto done;
	}

      } else {
	/*
	 * All equalities so far have the form (y == constant)
	 * - the current equality is (x == a)
	 */
	if (y == x) {
	  ivector_push(v, a); // match
	} else if (y == a && term_is_constant(terms, x)) {
	  ivector_push(v, x); // swap a and x
	} else {
	  // no match
	  goto done;
	}
      }
      neqs ++;
      break;

    case MATCH_IFF:
      /*
       * the returned term x is equivalent to r
       */
      push_term(queue, cache, x);
      break;

    default:
      // abort
      goto done;
    }
  } while (! int_queue_is_empty(queue));

  assert(t == NULL_TERM);

  // the same constant could occur several times in v:
  ivector_remove_duplicates(v);
  neqs = v->size;

  if (neqs >= 2) {
    assert(y != NULL_TERM && v->size == neqs);
    t = y;
  }

 done:
  int_queue_reset(queue);
  int_hset_reset(cache);

  return t;
}





/*
 * SUBSTITUTIONS
 */

/*
 * Initialize to the empty substitution:
 * - every constant is mapped to itself
 */
static void init_ctx_subst(ctx_subst_t *s, context_t *ctx) {
  uint32_t n;

  n = DEF_CTX_SUBST_SIZE;
  assert(n <= MAX_CTX_SUBST_SIZE);

  s->intern = &ctx->intern;
  s->terms = ctx->terms;
  s->subst = (term_t *) safe_malloc(n * sizeof(term_t));
  s->nterms = 0;
  s->size = n;
  init_term_manager(&s->mngr, ctx->terms);
  init_istack(&s->stack);
}


/*
 * Make sure s->subst is large enough to store s->subst[i]
 */
static void resize_ctx_subst(ctx_subst_t *s, uint32_t i) {
  uint32_t n;

  assert(i < UINT32_MAX);

  n = s->size;
  if (i >= n) {
    n += (n >> 1); // 50% larger
    if (i >= n) {
      n = i+1;
    }
    if (n > MAX_CTX_SUBST_SIZE) {
      out_of_memory();
    }
    s->subst = (term_t *) safe_realloc(s->subst, n * sizeof(term_t));
    s->size = n;
  }
}


/*
 * Store the mapping [i --> t] into subst
 */
static void ctx_subst_store(ctx_subst_t *s, uint32_t i, term_t t) {
  uint32_t j;

  if (i >= s->nterms) {
    // initialize s->subst[s->nterms to i-1]
    resize_ctx_subst(s, i);
    assert(i < s->size);
    for (j=s->nterms; j < i; j++) {
      s->subst[j] = NULL_TERM;
    }
    s->nterms = i+1;
  }
  s->subst[i] = t;
}


/*
 * Return s->subst[i] (NULL_TERM if not defined)
 */
static term_t ctx_subst_find(ctx_subst_t *s, uint32_t i) {
  return (i < s->nterms) ? s->subst[i] : NULL_TERM;
}


#if 0

// NOT USED
/*
 * Same thing for a term t: take polarity into account
 */
static term_t ctx_subst_of_term(ctx_subst_t *s, term_t t) {
  term_t u;

  assert(t >= 0 && intern_tbl_is_root(s->intern, t));
  u = ctx_subst_find(s, index_of(t));
  if (u >= 0) { // flip sign bit if t has negative sign
    u ^= polarity_of(t);
  }
  return u;
}

#endif

/*
 * Store the mapping t --> u in s
 */
static void set_ctx_subst_of_term(ctx_subst_t *s, term_t t, term_t u) {
  assert(t >= 0 && intern_tbl_is_root(s->intern, t));
  // if t has negative sign, replace u by not u:
  u ^= polarity_of(t);
  ctx_subst_store(s, index_of(t), u);
}


/*
 * Delete s
 */
static void delete_ctx_subst(ctx_subst_t *s) {
  safe_free(s->subst);
  s->subst = NULL;
  delete_term_manager(&s->mngr);
  delete_istack(&s->stack);
}


/*
 * Reset to the empty substitution
 */
static inline void reset_ctx_subst(ctx_subst_t *s) {
  s->nterms = 0;
  reset_istack(&s->stack);
}




/*
 * APPLY SUBSTITUTION
 */

/*
 * Get the term mapped to t in s
 * - raise an exception (by longjmp(s->env, -1) if something goes wrong
 *   (i.e., t is not in the QF_UF fragment)
 */
static term_t ctx_subst(ctx_subst_t *s, term_t t);


/*
 * apply the substitution s to all children of d
 * - return the result in an array allocated in s->stack
 */
static term_t *ctx_subst_children(ctx_subst_t *s, composite_term_t *d) {
  term_t *a;
  uint32_t i, n;

  n = d->arity;
  a= alloc_istack_array(&s->stack, n);
  for (i=0; i<n; i++) {
    a[i] = ctx_subst(s, d->arg[i]);
  }
  return a;
}

// (ite c t1 t2)
static term_t ctx_subst_ite(ctx_subst_t *s, composite_term_t *d) {
  term_table_t *terms;
  term_t c, t1, t2;
  type_t tau;
  term_t result;

  assert(d->arity == 3);

  c = ctx_subst(s, d->arg[0]);
  if (c == true_term) {
    result = ctx_subst(s, d->arg[1]);
  } else if (c == false_term) {
    result = ctx_subst(s, d->arg[2]);
  } else {
    t1 = ctx_subst(s, d->arg[1]);
    t2 = ctx_subst(s, d->arg[2]);

    terms = s->terms;
    tau = super_type(terms->types, term_type(terms, t1), term_type(terms, t2));
    assert(tau != NULL_TYPE);;

    result = mk_ite(&s->mngr, c, t1, t2, tau);
  }

  return result;
}

// (eq t1 t2)
static term_t ctx_subst_eq(ctx_subst_t *s, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = ctx_subst(s, d->arg[0]);
  t2 = ctx_subst(s, d->arg[1]);
  return mk_eq(&s->mngr, t1, t2);
}

// (or t1 .... tn)
static term_t ctx_subst_or(ctx_subst_t *s, composite_term_t *d) {
  term_t *a;
  term_t result;
  uint32_t i, n;

  n = d->arity;
  assert(n >= 2);

  a = alloc_istack_array(&s->stack, n);
  result = true_term;
  for (i=0; i<n; i++) {
    a[i] = ctx_subst(s, d->arg[i]);
    if (a[i] == true_term) goto done;
  }
  result = mk_or(&s->mngr, n, a);

 done:
  free_istack_array(&s->stack, a);

  return result;
}

// (xor t1 ... tn)
static term_t ctx_subst_xor(ctx_subst_t *s, composite_term_t *d) {
  term_t *a;
  term_t result;

  assert(d->arity >= 2);
  a = ctx_subst_children(s, d);
  result = mk_xor(&s->mngr, d->arity, a);
  free_istack_array(&s->stack, a);

  return result;
}

// (apply f t1 ... tn)
static term_t ctx_subst_app(ctx_subst_t *s, composite_term_t *d) {
  term_t *a;
  term_t result;

  assert(d->arity >= 2);

  a = ctx_subst_children(s, d);
  result = mk_application(&s->mngr, a[0], d->arity-1, a+1);
  free_istack_array(&s->stack, a);

  return result;
}

// (tuple t1 ... tn)
static term_t ctx_subst_tuple(ctx_subst_t *s, composite_term_t *d) {
  term_t *a;
  term_t result;

  assert(d->arity >= 1);

  a = ctx_subst_children(s, d);
  result = mk_tuple(&s->mngr, d->arity, a);
  free_istack_array(&s->stack, a);

  return result;
}

// (select t i)
static term_t ctx_subst_select(ctx_subst_t *s, select_term_t *d) {
  uint32_t idx;
  term_t t;

  idx = d->idx; // d may become invalid if new terms are created
  t = ctx_subst(s, d->arg);
  return mk_select(&s->mngr, t, idx);
}

// (distinct t1 ... tn)
static term_t ctx_subst_distinct(ctx_subst_t *s, composite_term_t *d) {
  term_t *a;
  term_t result;

  assert(d->arity >= 1);

  a = ctx_subst_children(s, d);
  result = mk_distinct(&s->mngr, d->arity, a);
  free_istack_array(&s->stack, a);

  return result;
}


static term_t ctx_subst(ctx_subst_t *s, term_t t) {
  term_table_t *terms;
  uint32_t polarity;
  term_t r, x;

  // replace t by its root in the internalization table
  r = intern_tbl_get_root(s->intern, t);
  polarity = polarity_of(r);
  r = unsigned_term(r);

  /*
   * Find what's mapped to r. Since r has positive polarity,
   * we can use ctx_subst_find directly.
   */
  x = ctx_subst_find(s, index_of(r));
  if (x == NULL_TERM) {
    terms = s->terms;
    switch (term_kind(terms, r)) {
    case CONSTANT_TERM:
    case UNINTERPRETED_TERM:
      x = r;
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
      x = ctx_subst_ite(s, ite_term_desc(terms, r));
      break;

    case EQ_TERM:
      x = ctx_subst_eq(s, eq_term_desc(terms, r));
      break;

    case OR_TERM:
      x = ctx_subst_or(s, or_term_desc(terms, r));
      break;

    case XOR_TERM:
      x = ctx_subst_xor(s, xor_term_desc(terms, r));
      break;

    case APP_TERM:
      x = ctx_subst_app(s, app_term_desc(terms, r));
      break;

    case TUPLE_TERM:
      x = ctx_subst_tuple(s, tuple_term_desc(terms, r));
      break;

    case SELECT_TERM:
      x = ctx_subst_select(s, select_term_desc(terms, r));
      break;

    case DISTINCT_TERM:
      x = ctx_subst_distinct(s, distinct_term_desc(terms, r));
      break;

    default:
      longjmp(s->env, -1);
      break;
    }

    assert(x != NULL_TERM);

    // store the mapping r --> x in s
    ctx_subst_store(s, index_of(r), x);
  }

  return x ^ polarity;
}



/*
 * Apply s to a[0 ... n-1]; store the result in b[0 ... n-1]
 */
static void ctx_subst_array(ctx_subst_t *s, term_t *a, term_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    b[i] = ctx_subst(s, a[i]);
  }
}


/*
 * Apply s to vectors ctx->top_eqs, ctx->top_atoms, ctx->top_formulas, ctx->subst_eqs, andc ctx->aux_eqs
 * - store the result in array a
 */
static void ctx_subst_assertions(ctx_subst_t *s, context_t *ctx, term_t *a) {
  ivector_t *v;
  uint32_t n;

  v = &ctx->top_eqs;
  n = v->size;
  ctx_subst_array(s, v->data, a, n);
  a += n;

  v = &ctx->top_atoms;
  n = v->size;
  ctx_subst_array(s, v->data, a, n);
  a += n;

  v = &ctx->top_formulas;
  n = v->size;
  ctx_subst_array(s, v->data, a, n);
  a += n;

  v = &ctx->subst_eqs;
  n = v->size;
  ctx_subst_array(s, v->data, a, n);
  a += n;

  v = &ctx->aux_eqs;
  n = v->size;
  ctx_subst_array(s, v->data, a, n);
}




/*
 * Build the substitution that swaps c0 and c1
 */
static void make_swap(ctx_subst_t *s, term_t c0, term_t c1) {
  reset_ctx_subst(s);
  set_ctx_subst_of_term(s, c0, c1);
  set_ctx_subst_of_term(s, c1, c0);
}


/*
 * Build circular substitution for c[0 ... n-1]
 * - subst(c[i+1]) = c[i]
 * - subst(c[0]) = c[n-1]
 */
static void make_cycle(ctx_subst_t *s, term_t *c, uint32_t n) {
  uint32_t i;

  reset_ctx_subst(s);
  set_ctx_subst_of_term(s, c[0], c[n-1]);
  for (i=1; i<n; i++) {
    set_ctx_subst_of_term(s, c[i], c[i-1]);
  }
}


/*
 * Check whether the assertions in ctx are invariant with respect
 * to permutations of the constants in array c
 * - n = size of c (must be >= 2)
 * - use s to build the substitutions
 */
static bool check_perm_invariance(context_t *ctx, ctx_subst_t *s, term_t *c, uint32_t n) {
  term_t *b;
  uint64_t num_assertions;
  uint32_t m;
  term_t norm1, norm2, norm3;
  int code;
  bool result;

  assert(n >= 2);

  /*
   * total number of assertions
   * we check that it's no more than MAX_ARITY.
   * If we have more than MAX_ARITY assertions, we may fail to build norm1, norm2, norm3.
   */
  num_assertions = (uint64_t) ctx->top_eqs.size +  (uint64_t) ctx->top_atoms.size + (uint64_t) ctx->top_formulas.size +
    + (uint64_t) ctx->subst_eqs.size + (uint64_t) ctx->aux_eqs.size;
  if (num_assertions > (uint64_t) YICES_MAX_ARITY) {
    return false;
  }

  assert(num_assertions <= (uint64_t) UINT32_MAX);

  m = (uint32_t) num_assertions;
  b = (term_t *) safe_malloc(m * sizeof(term_t));

  result = false;

  code = setjmp(s->env);
  if (code == 0) {
    // empty substitution = normalize the assertions
    reset_ctx_subst(s);
    ctx_subst_assertions(s, ctx, b);
    norm1 = mk_and(&s->mngr, m, b);

#if TRACE
    printf("perm invariance: norm1\n");
    pretty_print_term_full(stdout, NULL, ctx->terms, norm1);
#endif

    // swap c[0] and c[1]
    make_swap(s, c[0], c[1]);
    ctx_subst_assertions(s, ctx, b);
    norm2 = mk_and(&s->mngr, m, b);

#if TRACE
    printf("perm invariance: norm2\n");
    pretty_print_term_full(stdout, NULL, ctx->terms, norm2);
#endif

    if (norm1 != norm2) goto done;

    // circular substitution
    make_cycle(s, c, n);
    ctx_subst_assertions(s, ctx, b);
    norm3 = mk_and(&s->mngr, m, b);

#if TRACE
    printf("perm invariance: norm3\n");
    pretty_print_term_full(stdout, NULL, ctx->terms, norm3);
#endif

    result = (norm1 == norm3);
  } else {
    // exception
    assert(! result);
  }

 done:
  safe_free(b);
  return result;
}





/*
 * COLLECT CONSTANTS IN TERMS
 */

#ifndef NDEBUG
static bool sorted_array(term_t *c, uint32_t n) {
  uint32_t i;

  for (i=1; i<n; i++) {
    if (c[i-1] >= c[i]) return false;
  }
  return true;
}
#endif


/*
 * Check whether a belongs to array c[0 ... n-1]
 * - c must be sorted in strict increasing order
 * - return true if a is in the array and store a's position
 *   in *j.
 */
static bool constant_is_in_set(term_t a, term_t *c, uint32_t n, uint32_t *j) {
  uint32_t l, h, k;

  assert(n > 0 && sorted_array(c, n));

  l = 0;
  h = n;
  for (;;) {
    k = (l + h)/2;
    assert(l <= k && k < h);
    if (k == l) break;
    if (a < c[k]) {
      h = k;
    } else {
      l = k;
    }
  }

  *j = k;
  return c[k] == a;
}


/*
 * Collect all constants of c[0 ... n-1] that occur in t
 * - store their indices in vector v
 * - side effect: use breaker->queue and breaker->cache
 */
static void collect_constants(sym_breaker_t *breaker, term_t t, term_t *c, uint32_t n, ivector_t *v) {
  int_queue_t *queue;
  int_hset_t *cache;
  term_table_t *terms;
  intern_tbl_t *intern;
  term_t r;
  uint32_t k;

  queue = &breaker->queue;
  cache = &breaker->cache;
  terms = breaker->terms;
  intern = &breaker->ctx->intern;

  ivector_reset(v);

  assert(int_queue_is_empty(queue) && int_hset_is_empty(cache));
  push_term(queue, cache, t);

  do {
    // r := root of the first term in the queue
    r = intern_tbl_get_root(intern, int_queue_pop(queue));
    switch (term_kind(terms, r)) {
    case UNUSED_TERM:
    case RESERVED_TERM:
      assert(false);
      abort();
      break;

    case CONSTANT_TERM:
    case UNINTERPRETED_TERM:
      if (constant_is_in_set(r, c, n, &k)) {
        assert(0 <= k && k < n && c[k] == r);
        ivector_push(v, k);
      }
      break;

    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
    case VARIABLE:
      // ignore it
      break;

    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
    case ARITH_IS_INT_ATOM:
    case ARITH_FLOOR:
    case ARITH_CEIL:
    case ARITH_ABS:
      push_term(queue, cache, arith_atom_arg(terms, r));
      break;

    case ARITH_ROOT_ATOM:
      // ignore it
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case APP_TERM:
    case UPDATE_TERM:
    case TUPLE_TERM:
    case EQ_TERM:
    case DISTINCT_TERM:
    case OR_TERM:
    case XOR_TERM:
    case ARITH_BINEQ_ATOM:
    case ARITH_RDIV:
    case ARITH_IDIV:
    case ARITH_MOD:
    case ARITH_DIVIDES_ATOM:
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
      push_children(queue, cache, composite_term_desc(terms, r));
      break;

    case FORALL_TERM:
    case LAMBDA_TERM:
      push_last_child(queue, cache, composite_term_desc(terms, r));
      break;

    case SELECT_TERM:
    case BIT_TERM:
      push_term(queue, cache, select_for_idx(terms, index_of(r))->arg);
      break;

    case POWER_PRODUCT:
      push_pprod_vars(queue, cache, pprod_term_desc(terms, r));
      break;

    case ARITH_POLY:
      push_poly_vars(queue, cache, poly_term_desc(terms, r));
      break;

    case BV64_POLY:
      push_bvpoly64_vars(queue, cache, bvpoly64_term_desc(terms, r));
      break;

    case BV_POLY:
      push_bvpoly_vars(queue, cache, bvpoly_term_desc(terms, r));
      break;

    case ARITH_FF_POLY:
    case ARITH_FF_CONSTANT:
    case ARITH_FF_EQ_ATOM:
    case ARITH_FF_BINEQ_ATOM:
      longjmp(breaker->ctx->env, CONTEXT_UNSUPPORTED_THEORY);
      break;
    }
  } while (! int_queue_is_empty(queue));

  int_queue_reset(queue);
  int_hset_reset(cache);
}




/*
 * SETS OF CONSTANTS AND CANDIDATES
 */

/*
 * Initialization: don't allocate anything yet.
 */
static void init_sym_breaker_sets(sym_breaker_sets_t *s) {
  s->constants = NULL;
  s->num_constants = 0;
  init_cset(&s->available);
  init_cset(&s->removed);
  s->used = NULL;
  s->num_used = 0;
  s->used_size = 0;
  s->candidates = NULL;
  s->cost = NULL;
  s->hash = NULL;
  s->num_candidates = 0;
  s->candidate_size = 0;
}


/*
 * Make array used large enough for n elements
 */
static void resize_used_set(sym_breaker_sets_t *s, uint32_t n) {
  assert(n <= MAX_SBREAK_SET_SIZE);

  if (s->used_size < n) {
    s->used = (term_t *) safe_realloc(s->used, n * sizeof(term_t));
    s->used_size = n;
  }
}

/*
 * Make the candidate arrays large enough for n elements
 */
static void resize_candidate_set(sym_breaker_sets_t *s, uint32_t n) {
  assert(n <= MAX_SBREAK_SET_SIZE);

  if (s->candidate_size < n) {
    s->candidates = (term_t *) safe_realloc(s->candidates, n * sizeof(term_t));
    s->cost = (uint32_t *) safe_realloc(s->cost, n * sizeof(uint32_t));
    s->hash = (uint32_t *) safe_realloc(s->hash, n * sizeof(uint32_t));
    s->candidate_size = n;
  }
}



/*
 * Free everything
 */
static void delete_sym_breaker_sets(sym_breaker_sets_t *s) {
  delete_cset(&s->available);
  delete_cset(&s->removed);
  safe_free(s->used);
  safe_free(s->candidates);
  safe_free(s->cost);
  safe_free(s->hash);
  s->used = NULL;
  s->candidates = NULL;
  s->cost = NULL;
  s->hash = NULL;
}


/*
 * Copy array of constants c[0 ... n-1] into s
 * - c must be sorted and fixed
 */
static void copy_constant_set(sym_breaker_sets_t *s, term_t *c, uint32_t n) {
  if (s->constants != NULL) {
    // required before we can call cset_init_full & cset_init_empty.
    reset_cset(&s->available);
    reset_cset(&s->removed);
  }
  s->constants = c;
  s->num_constants = n;
  cset_init_full(&s->available, n);
  cset_init_empty(&s->removed, n);
  resize_used_set(s, n);
  s->num_used = 0;
}


/*
 * Copy array of candidates t[0 ... n-1] into s
 */
static void copy_candidate_set(sym_breaker_sets_t *s, term_t *t, uint32_t n) {
  uint32_t i;

  resize_candidate_set(s, n);
  for (i=0; i<n; i++) {
    s->candidates[i] = t[i];
  }
  s->num_candidates = n;
}


/*
 * Add more candidates
 */
static void add_candidate_set(sym_breaker_sets_t *s, term_t *t, uint32_t n) {
  uint32_t i, new_size;
  term_t *d;

  assert(n <= MAX_SBREAK_SET_SIZE);

  new_size = n + s->num_candidates;
  if (new_size > MAX_SBREAK_SET_SIZE) {
    out_of_memory();
  }
  resize_candidate_set(s, new_size);
  d = s->candidates + s->num_candidates;
  for (i=0; i<n; i++) {
    d[i] = t[i];
  }
  s->num_candidates = new_size;
}


/*
 * Remove s->candidates[i] from the set
 */
static void remove_candidate(sym_breaker_sets_t *s, uint32_t i) {
  uint32_t j;

  assert(0 <= i && i < s->num_candidates);
  j = s->num_candidates - 1;
  if (i < j) {
    // move last element into position i
    s->candidates[i] = s->candidates[j];
    s->cost[i] = s->cost[j];
    s->hash[i] = s->hash[j];
  }
  s->num_candidates = j;
}



/*
 * Get the set of constants of term candidates[i] and compute cost and hash
 */
static void compute_cost(sym_breaker_t *breaker, sym_breaker_sets_t *s, uint32_t i) {
  ivector_t *v;
  uint32_t j, k, n, cost, hash;

  assert(i < s->num_candidates);
  v = &breaker->aux;
  collect_constants(breaker, s->candidates[i], s->constants, s->num_constants, v);

  hash = 0;
  cost = 0;
  n = v->size;
  for (j=0; j<n; j++) {
    k = v->data[j];
    if (cset_member(&s->available, k)) {
      cost ++;
      hash |= ((uint32_t) 1) << (k & 0x1f);
    }
  }
  s->cost[i] = cost;
  s->hash[i] = hash;
}


/*
 * Compute all the costs: must be call after the set of candidates is set
 */
static void compute_costs(sym_breaker_t *breaker, sym_breaker_sets_t *s) {
  uint32_t i, n;

  n = s->num_candidates;
  for (i=0; i<n; i++) {
    compute_cost(breaker, s, i);
  }
}


/*
 * Update the cost of i based on the removed set:
 * - removed = set of constants that were moved from available to used
 * - let C[i] = set of constants of candidate[i]
 *       D[i] = C[i] \inter old available set
 *       E[i] = C[i] \inter new available set
 * - we have new available set = old available set - removed
 *   So if removed \inter D[i] is empty, we know that E[i] = D[i]
 *   and cost[i] does not change.
 * - We check whether hash[i] & removed->hash is 0. If so, we know that
 *   D[i] inter removed is empty.
 */
static void update_cost(sym_breaker_t *breaker, sym_breaker_sets_t *s, uint32_t i) {
  assert(i < s->num_candidates);
  if ((s->hash[i] & s->removed.hash) != 0) {
    compute_cost(breaker, s, i);
  }
}


/*
 * Update all the costs
 */
static void update_costs(sym_breaker_t *breaker, sym_breaker_sets_t *s) {
  uint32_t i, n;

  n = s->num_candidates;
  for (i=0; i<n; i++) {
    update_cost(breaker, s, i);
  }
}



/*
 * Select a term t from s->candidates then remove t from the candidate set.
 * - heuristic: terms with lower cost are preferred, in case of ties (equal costs)
 *   t is preferred over u if t is a constant and u is not
 * - return NULL_TERM if nothing is found
 */
static term_t select_candidate(sym_breaker_t *breaker, sym_breaker_sets_t *s) {
  uint32_t j, n, min_so_far;
  uint32_t i;
  uint32_t cost;
  term_t t;

  n = s->num_candidates;
  if (n == 0) {
    return NULL_TERM;
  }

  min_so_far = UINT32_MAX;;
  j = n; // stop GCC warning

  for (i=0; i<n; i++) {
    t = s->candidates[i];
    cost = s->cost[i];
    if (cost <= min_so_far) {
      if (term_is_constant(breaker->terms, t)) {
	j = i;
	break;
      } else if (cost < min_so_far) {
	min_so_far = cost;
	j = i;
      }
    }
  }

  assert(j < s->num_candidates);
  t = s->candidates[j];
  remove_candidate(s, j);

  return t;
}



/*
 * Move the constants:
 * - remove all elements of 'removed' from 'available'
 * - add them to 'used'
 */
static void move_constants(sym_breaker_t *breaker, sym_breaker_sets_t *s) {
  ivector_t *v;
  uint32_t i, j, n;
  term_t c;

  assert(cset_subset(&s->removed, &s->available));
  cset_remove_set(&s->available, &s->removed);

  // append remove to array s->used
  v = &breaker->aux;
  ivector_reset(v);
  cset_extract(&s->removed, v);

  j = s->num_used;
  n  = v->size;
  for (i=0; i<n; i++) {
    assert(0 <= v->data[i] && v->data[i] < s->num_constants);
    c = s->constants[v->data[i]];
    s->used[j] = c;
    j ++;
  }
  s->num_used = j;
}



/*
 * Collect all constants of term t
 * - add the constants that are in s->available to s->remove
 */
static void remove_constants_of_term(sym_breaker_t *breaker, sym_breaker_sets_t *s, term_t t) {
  ivector_t *v;
  uint32_t i, n, j;

  cset_empty(&s->removed);

  v = &breaker->aux;
  collect_constants(breaker, t, s->constants, s->num_constants, v);
  n = v->size;
  for (i=0; i<n; i++) {
    j = v->data[i];
    if (cset_member(&s->available, j)) {
      cset_add(&s->removed, j);
    }
  }
  ivector_reset(v);
}


/*
 * SYMMETRY-BREAKING CLAUSES
 */
/*
 * Build the equality term: (= t c)
 */
static term_t make_aux_eq(term_table_t *terms, term_t t, term_t c) {
  term_t aux;

  if (t > c) {
    // normalize (cf. term_manager.c)
    aux = t; t = c; c = aux;
  }
  assert(t < c);
  return eq_term(terms, t, c);
}


/*
 * Add the clause (or (= t c[0]) .... (= t c[n-1]))
 * - t and all elements of c must be root terms in ctx->intern
 * - n must be positive
 * - the terms (= t c[i]) must not simplify to false
 *
 * Side effect: uses break->aux
 *
 * Precaution: if (or (= t c[0]) ... (= t c[n-1])) is already
 * internalized, we do nothing to make sure we're doing something
 * sound.
 */
static void add_symmetry_breaking_clause(sym_breaker_t *breaker, term_t t, term_t *c, uint32_t n) {
  term_table_t *terms;
  context_t *ctx;
  intern_tbl_t *intern;
  ivector_t *v;
  term_t eq, or;
  uint32_t i;

  terms = breaker->terms;
  ctx = breaker->ctx;
  intern = &ctx->intern;

  assert(intern_tbl_is_root(intern, t));

  if (n == 1) {
    /*
     * special case: we add (= t c[0]) as an auxiliary equality
     */
    add_aux_eq(ctx, t, c[0]);

#if TRACE
    printf("Adding symmetry-breaking constraint\n");
    pretty_print_term_full(stdout, NULL, terms, make_aux_eq(terms, t, c[0]));
    printf("\n");
#endif
    trace_puts(ctx->trace, 5, "Adding symmetry-breaking constraint\n");
    trace_pp_term(ctx->trace, 5, terms, make_aux_eq(terms, t, c[0]));

  } else {
    v = &breaker->aux;
    ivector_reset(v);

    for (i=0; i<n; i++) {
      assert(intern_tbl_is_root(intern, c[i]));
      eq = make_aux_eq(terms, t, c[i]);
      assert(intern_tbl_is_root(intern, eq));

      ivector_push(v, eq);
    }

    /*
     * build (or v->data[0] ... v->data[n])
     * add it as a top-level formula
     */
    int_array_sort(v->data, n);
    or = or_term(terms, n, v->data);
    assert(intern_tbl_is_root(intern, or) && !term_is_false(ctx, or));

#if TRACE
    printf("Symmetry breaking constraint\n");
    pretty_print_term_full(stdout, NULL, terms, or);
    if (intern_tbl_root_is_mapped(intern, or)) {
      printf("Redundant\n\n");
    } else {
      printf("Added\n\n");
    }
#endif

    if (! intern_tbl_root_is_mapped(intern, or)) {
      intern_tbl_map_root(intern, or, bool2code(true));
      ivector_push(&ctx->top_formulas, or);

      trace_puts(ctx->trace, 5, "Adding symmetry-breaking constraint\n");
      trace_pp_term(ctx->trace, 5, terms, or);
    }

    ivector_reset(v);
  }

}





/*
 * Check whether term (= t c) is false
 */
static bool aux_eq_is_false(sym_breaker_t *breaker, term_t t, term_t c) {
  term_t eq;

  eq = make_aux_eq(breaker->terms, t, c);
  return term_is_false(breaker->ctx, eq);
}


/*
 * Search for a constant c in s->constants such that
 * 1) c is in s->available and not in s->removed
 * 2) (eq t c) is not false
 * - return c's index or -1 if nothing is found
 */
static int32_t select_constant_for_term(sym_breaker_t *breaker, sym_breaker_sets_t *s, term_t t) {
  uint32_t i, n;
  term_t c;

  n = s->num_constants;
  for (i=0; i<n; i++) {
    if (cset_member(&s->available, i) && !cset_member(&s->removed, i)) {
      c = s->constants[i];
      if (! aux_eq_is_false(breaker, t, c)) {
	return i;
      }
    }
  }

  return -1;
}


/*
 * Attempt to add a symmetry-breaking clause for term t
 * - update the set of constants/used constants
 * - side effect: use breaker->aux
 */
static void break_symmetries_for_term(sym_breaker_t *breaker, sym_breaker_sets_t *s, term_t t) {
  int32_t k;

  remove_constants_of_term(breaker, s, t);
  k = select_constant_for_term(breaker, s, t);
  if (k >= 0) {
    // success: found a usable constant
    cset_add(&s->removed, k);   // add k to removed
    move_constants(breaker, s); // copy all removed constants from available to used
    add_symmetry_breaking_clause(breaker, t, s->used, s->num_used); // add the clause

    update_costs(breaker, s);  // update the costs
  }
}



/*
 * Break symmetries based on constant and candidate sets s
 */
void break_symmetries(sym_breaker_t *breaker, sym_breaker_sets_t *s) {
  term_t t;

  compute_costs(breaker, s);

  while (! cset_is_empty(&s->available)) {
    t = select_candidate(breaker, s);
    if (t == NULL_TERM) break; // no candidates
    break_symmetries_for_term(breaker, s, t);
  }
}






/*
 * SYMMETRY BREAKER
 */

/*
 * Initialize sym_breaker
 * - ctx = relevant context
 */
void init_sym_breaker(sym_breaker_t *breaker, context_t *ctx) {
  breaker->ctx = ctx;
  breaker->terms = ctx->terms;
  init_rng_vector(&breaker->range_constraints);
  breaker->sorted_constraints = NULL;
  breaker->num_constraints = 0;
  init_sym_breaker_sets(&breaker->sets);
  init_int_queue(&breaker->queue, 0);
  init_int_hset(&breaker->cache, 0);
  init_ivector(&breaker->aux, 10);
}


/*
 * Delete it: free all memory it uses
 */
void delete_sym_breaker(sym_breaker_t *breaker) {
  delete_rng_vector(&breaker->range_constraints);
  safe_free(breaker->sorted_constraints);
  delete_sym_breaker_sets(&breaker->sets);
  delete_int_queue(&breaker->queue);
  delete_int_hset(&breaker->cache);
  delete_ivector(&breaker->aux);
}


/*
 * Build the sorted array of constraints
 */
// ordering: r1 > r2  if r1->num_cst > r2->num_cst
static bool gt_cnstr(void *aux, void *x, void *y) {
  return ((rng_record_t *) x)->num_constants > ((rng_record_t *) y)->num_constants;
}

static void sort_range_constraints(sym_breaker_t *breaker) {
  uint32_t i, n;
  rng_record_t **tmp;

  assert(breaker->sorted_constraints == NULL && breaker->num_constraints == 0);

  n = breaker->range_constraints.nelems;
  if (n > 0) {
    tmp = (rng_record_t **) safe_malloc(n * sizeof(rng_record_t *));
    for (i=0; i<n; i++) {
      tmp[i] = breaker->range_constraints.data + i;
    }
    ptr_array_sort2((void **) tmp, n, NULL, gt_cnstr);

    breaker->sorted_constraints = tmp;
    breaker->num_constraints = n;
  }
}


/*
 * Collect all domain constraints from ctx->top_formulas
 * - all constraints found are added to the range_constraint record
 */
void collect_range_constraints(sym_breaker_t *breaker) {
  ivector_t *formulas;
  ivector_t *v;
  uint32_t i, n;
  term_t t;

  v = &breaker->aux;
  formulas = &breaker->ctx->top_formulas;
  n = formulas->size;
  for (i=0; i<n; i++) {
    ivector_reset(v);
    t = formula_is_range_constraint(breaker, formulas->data[i], v);
    if (t != NULL_TERM) {
      //      int_array_sort(v->data, v->size); // sort the constants
      assert(sorted_array(v->data, v->size));
      add_range_constraint(&breaker->range_constraints, v->data, v->size, t, i);
    }
  }

  sort_range_constraints(breaker);
}




/*
 * Check whether the assertions are invariant by permutation of
 * constants in record r.
 */
bool check_assertion_invariance(sym_breaker_t *breaker, rng_record_t *r) {
  ctx_subst_t subst;
  bool result;

  init_ctx_subst(&subst, breaker->ctx);
  result = check_perm_invariance(breaker->ctx, &subst, r->cst, r->num_constants);
  delete_ctx_subst(&subst);

  return result;
}



/*
 * Initialize set s from r
 */
void breaker_sets_copy_record(sym_breaker_sets_t *s, rng_record_t *r) {
  copy_constant_set(s, r->cst, r->num_constants);
  copy_candidate_set(s, r->trm, r->num_terms);
}


/*
 * Add all terms of r to s->candidates
 */
void breaker_sets_add_record(sym_breaker_sets_t *s, rng_record_t *r) {
  add_candidate_set(s, r->trm, r->num_terms);
}


