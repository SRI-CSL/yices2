/*
 * Data structure to support term substitution
 */

#include <assert.h>

#include "memalloc.h"
#include "bvarith_buffer_terms.h"
#include "bvarith64_buffer_terms.h"

#include "term_substitution.h"

/*
 * Check whether t is either an uninterpreted term
 * - t must be a good positive term
 */
static bool term_is_var(term_table_t *terms, term_t t) {
  assert(good_term(terms, t) && is_pos_term(t));
  return term_kind(terms, t) == UNINTERPRETED_TERM;
}

/*
 * Check whether arrays v and t define a valid substitution:
 * - v and t must be arrays of n terms
 * - this returns true if forall i, v[i] is a variable
 *   and the type of t[i] is a subtype of v[i]'s type.
 */
bool good_term_subst(term_table_t *terms, uint32_t n, term_t *v, term_t *t) {
  type_table_t *types;
  uint32_t i;
  term_t x, u;

  types = terms->types;
  for (i=0; i<n; i++) {
    x = v[i];
    u = t[i];
    assert(good_term(terms, x) && good_term(terms, u));
    if (is_neg_term(x) || !term_is_var(terms, x) ||
        !is_subtype(types, term_type(terms, u), term_type(terms, x))) {
      return false;
    }
  }

  return true;
}


/*
 * Initialize subst: store the mapping v[i] --> t[i]
 */
void init_term_subst(term_subst_t *subst, term_manager_t *mngr, uint32_t n, term_t *v, term_t *t) {
  int_hmap_pair_t *p;
  uint32_t i;
  term_t x;

  assert(good_term_subst(term_manager_get_terms(mngr), n, v, t));

  subst->mngr = mngr;
  subst->terms = term_manager_get_terms(mngr);
  init_int_hmap(&subst->map, 0);
  init_subst_cache(&subst->cache);
  init_istack(&subst->stack);

  for (i=0; i<n; i++) {
    x = v[i];
    assert(is_pos_term(x) && term_is_var(subst->terms, x) &&
	   good_term(subst->terms, t[i]));
    p = int_hmap_get(&subst->map, x);
    p->val = t[i];
  }
}




/*
 * Delete: free all memory used
 */
void delete_term_subst(term_subst_t *subst) {
  delete_int_hmap(&subst->map);
  delete_subst_cache(&subst->cache);
  delete_istack(&subst->stack);
}



/*
 * UTILITIES
 */

/*
 * Lookup the term mapped to x where x is uninterpreted
 * - lookup x in the map
 * - if x is not there return x
 */
static term_t get_subst_of_unint(term_subst_t *subst, term_t x) {
  int_hmap_pair_t *p;
  term_t y;

  assert(is_pos_term(x) && term_kind(subst->terms, x) == UNINTERPRETED_TERM);

  y = x;
  p = int_hmap_find(&subst->map, x);
  if (p != NULL) {
    y = p->val;
  }

  return y;
}


/*
 * Check whether the result of subst(t) is stored in the cache
 * - t must be a valid term in subst->terms
 * - this takes the renaming context into account
 * - return NULL_TERM (-1) is the result is not in the cache
 */
static term_t get_cached_subst(term_subst_t *subst, term_t t) {
  assert(is_pos_term(t) && good_term(subst->terms, t));
  return subst_cache_lookup(&subst->cache, NULL, t);
}


/*
 * Add u as subst(t) in the cache
 * - t and u must be valid terms in subst->terms
 * - there must not be an existing value for t in the cache
 */
static void cache_subst_result(term_subst_t *subst, term_t t, term_t u) {
  assert(is_pos_term(t) && good_term(subst->terms, t) && good_term(subst->terms, u));
  subst_cache_add(&subst->cache, NULL, t, u);
}




/*
 * BUILD POWER PRODUCTS AND POLYNOMIAL TERMS
 */

/*
 * Check whether the product a[0]^e_0 ... a[n-1]^e_{n-1} has degree > YICEX_MAX_DEGREE
 * - e_i = exponent in pprod p
 */
static bool pprod_degree_overflows(term_table_t *tbl, pprod_t *p, uint32_t n, term_t *a) {
  uint64_t d;
  uint32_t i;

  assert(n == p->len);

  d = 0;
  for (i=0; i<n; i++) {
    d += ((uint64_t) term_degree(tbl, a[i])) * p->prod[i].exp;
    if (d > (uint64_t) YICES_MAX_DEGREE) {
      return true;
    }
  }

  return false;
}


/*
 * Check whether term t is 0
 * - t is a bitvector term
 */
static bool term_is_zero(term_table_t *tbl, term_t t) {
  bvconst_term_t *c;
  uint32_t k;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    return bvconst64_term_desc(tbl, t)->value == (uint64_t) 0;

  case BV_CONSTANT:
    c = bvconst_term_desc(tbl, t);
    k = (c->bitsize + 31) >> 5;
    return bvconst_is_zero(c->data, k);

  default:
    return false;
  }
}


/*
 * Bitvector product: 1 to 64 bits vector
 * - p is a power product descriptor: t_0^e_0 ... t_{n-1}^e_{n-1}
 * - a is an array of n arithmetic terms: a[i] = subst of t_i
 * - nbits = number of bits in each term
 * - this function constructs the term a[0]^e_0 ... a[n-1]^e_{n-1}
 */
static term_t bvarith64_pprod(term_manager_t *mngr, pprod_t *p, uint32_t n, term_t *a, uint32_t nbits) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  assert(n == p->len && 0 < nbits && nbits <= 64);

  tbl = term_manager_get_terms(mngr);
  b = term_manager_get_bvarith64_buffer(mngr);

  bvarith64_buffer_prepare(b, nbits);
  bvarith64_buffer_set_one(b); // b := 1
  for (i=0; i<n; i++) {
    // b := b * a[i]^e[i]
    bvarith64_buffer_mul_term_power(b, tbl, a[i], p->prod[i].exp);
  }

  return mk_bvarith64_term(mngr, b);
}


/*
 * Bitvector product: more than 64 bits
 * - p is a power product descriptor: t_0^e_0 ... t_{n-1}^e_{n-1}
 * - a is an array of n arithmetic terms: a[i] = subst of t_i
 * - nbits = number of bits in each term
 * - this function constructs the term a[0]^e_0 ... a[n-1]^e_{n-1}
 */
static term_t bvarith_pprod(term_manager_t *mngr, pprod_t *p, uint32_t n, term_t *a, uint32_t nbits) {
  bvarith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  assert(n == p->len && 64 < nbits && nbits <= YICES_MAX_BVSIZE);

  tbl = term_manager_get_terms(mngr);
  b = term_manager_get_bvarith_buffer(mngr);

  bvarith_buffer_prepare(b, nbits);
  bvarith_buffer_set_one(b); // b := 1
  for (i=0; i<n; i++) {
    // b := b * a[i]^e[i]
    bvarith_buffer_mul_term_power(b, tbl, a[i], p->prod[i].exp);
  }

  return mk_bvarith_term(mngr, b);
}


/*
 * Bit vector polynomial:
 * - p is a polynomial c_0 t_0 + c_1 t_1 + ... + c_{n-1} t_{n-1}
 * - a is an array of n terms: a[i] = subst of t_i
 *   except that a[0] = const_idx if t_0 = const_idx
 * - construct the term c_0 a[0] + c_1 a[1] + ... + c_{n-1} a[n-1]
 *   (or c_0 + c_1 a[1] + ... + c_{n-1} a[n-1] if a[0] = const_idx)
 *
 * Coefficients c0 ... c_{n-1} are bitvector constants with no more than 64bits
 */
static term_t build_bvarith64_poly(term_manager_t *mngr, bvpoly64_t *p, uint32_t n, term_t *a) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  assert(p->nterms == n && 0 < p->bitsize && p->bitsize <= 64);

  tbl = term_manager_get_terms(mngr);
  b = term_manager_get_bvarith64_buffer(mngr);
  bvarith64_buffer_prepare(b, p->bitsize);

  // deal with the constant
  i = 0;
  if (a[i] == const_idx) {
    assert(p->mono[0].var == const_idx);
    bvarith64_buffer_add_const(b, p->mono[0].coeff);
    i ++;
  }

  // rest
  while (i < n) {
    bvarith64_buffer_add_const_times_term(b, tbl, p->mono[i].coeff, a[i]);
    i ++;
  }

  return mk_bvarith64_term(mngr, b);
}


/*
 * Same thing for polynomials with coefficients more than 64bits
 */
static term_t build_bvarith_poly(term_manager_t *mngr, bvpoly_t *p, uint32_t n, term_t *a) {
  bvarith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  assert(p->nterms == n && 64 < p->bitsize && p->bitsize <= YICES_MAX_BVSIZE);

  tbl = term_manager_get_terms(mngr);
  b = term_manager_get_bvarith_buffer(mngr);
  bvarith_buffer_prepare(b, p->bitsize);

  // deal with the constant
  i = 0;
  if (a[i] == const_idx) {
    assert(p->mono[0].var == const_idx);
    bvarith_buffer_add_const(b, p->mono[0].coeff);
    i ++;
  }

  // rest
  while (i < n) {
    bvarith_buffer_add_const_times_term(b, tbl, p->mono[i].coeff, a[i]);
    i ++;
  }

  return mk_bvarith_term(mngr, b);
}



/*
 * APPLY SUBSTITUTION
 */

/*
 * Main recursive function
 * - apply 'subst' to 't': return the result
 *
 * Error codes returned:
 * - if the substitution creates a term of degree > YICES_MAX_DEGREE
 *   abort by calling longjmp(subst->env): return -1 (NULL_TERM)
 * - if something else goes wrong (either because the substitution is wrong
 *   or there's a bug somewhere): return -2
 */
static term_t get_subst(term_subst_t *subst, term_t t);


/*
 * Auxiliary function: apply subst recursively to all children of d
 * - return the result in array a, allocated in the subst->stack
 */
static term_t *subst_children(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  uint32_t i, n;

  n = d->arity;
  a = alloc_istack_array(&subst->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_subst(subst, d->arg[i]);
  }

  return a;
}


/*
 * Substitution for all other composite terms
 */

// (ite c t1 t2)
static term_t subst_ite(term_subst_t *subst, composite_term_t *d) {
  term_table_t *tbl;
  term_t c, t1, t2;
  type_t tau;
  term_t result;

  assert(d->arity == 3);

  c = get_subst(subst, d->arg[0]); // condition
  if (c == true_term) {
    result = get_subst(subst, d->arg[1]);
  } else if (c == false_term) {
    result = get_subst(subst, d->arg[2]);
  } else {
    t1 = get_subst(subst, d->arg[1]);
    t2 = get_subst(subst, d->arg[2]);

    tbl = subst->terms;
    tau = super_type(tbl->types, term_type(tbl, t1), term_type(tbl, t2));
    assert(tau != NULL_TYPE);

    result = mk_ite(subst->mngr, c, t1, t2, tau);
  }

  return result;
}

// equality
static term_t subst_eq(term_subst_t *subst, composite_term_t *d) {
  term_t t, u;

  assert(d->arity == 2);
  t = get_subst(subst, d->arg[0]);
  u = get_subst(subst, d->arg[1]);
  return mk_eq(subst->mngr, t, u);
}

// distinct
static term_t subst_distinct(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  term_t result;

  a = subst_children(subst, d);
  result = mk_distinct(subst->mngr, d->arity, a);
  free_istack_array(&subst->stack, a);

  return result;
}

// or
static term_t subst_or(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  term_t result;
  uint32_t i, n;

  n = d->arity;
  assert(n >= 2);

  a = alloc_istack_array(&subst->stack, n);
  result = true_term;
  for (i=0; i<n; i++) {
    a[i] = get_subst(subst, d->arg[i]);
    if (a[i] == true_term) goto done; // result is true_term
  }

  // no simplification:
  result = mk_or(subst->mngr, n, a);

 done:
  free_istack_array(&subst->stack, a);

  return result;
}

// xor
static term_t subst_xor(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  term_t result;

  assert(d->arity >= 2);
  a = subst_children(subst, d);
  result = mk_xor(subst->mngr, d->arity, a);
  free_istack_array(&subst->stack, a);

  return result;
}

// array of bits
static term_t subst_bvarray(term_subst_t *subst, composite_term_t *d) {
  term_t *a;
  term_t result;

  assert(d->arity >= 1);
  a = subst_children(subst, d);
  result = mk_bvarray(subst->mngr, d->arity, a);
  free_istack_array(&subst->stack, a);

  return result;
}

// bitvector division and shift operators
static term_t subst_bvdiv(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvdiv(subst->mngr, t1, t2);
}

static term_t subst_bvrem(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvrem(subst->mngr, t1, t2);
}

static term_t subst_bvsdiv(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvsdiv(subst->mngr, t1, t2);
}

static term_t subst_bvsrem(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvsrem(subst->mngr, t1, t2);
}

static term_t subst_bvsmod(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvsmod(subst->mngr, t1, t2);
}

static term_t subst_bvshl(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvshl(subst->mngr, t1, t2);
}

static term_t subst_bvlshr(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvlshr(subst->mngr, t1, t2);
}

static term_t subst_bvashr(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvashr(subst->mngr, t1, t2);
}

// bitvector atoms
static term_t subst_bveq(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bveq(subst->mngr, t1, t2);
}

static term_t subst_bvge(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvge(subst->mngr, t1, t2);
}

static term_t subst_bvsge(term_subst_t *subst, composite_term_t *d) {
  term_t t1, t2;

  assert(d->arity == 2);
  t1 = get_subst(subst, d->arg[0]);
  t2 = get_subst(subst, d->arg[1]);
  return mk_bvsge(subst->mngr, t1, t2);
}

/*
 * bit select
 *
 * Warning: d is not a safe pointer (it may become invalid if new
 * terms are created). cf. terms.h
 *
 * So we must make a copy of d->idx before the recursive call
 */
static term_t subst_bit_select(term_subst_t *subst, select_term_t *d) {
  uint32_t idx;
  term_t t;

  idx = d->idx;
  t = get_subst(subst, d->arg);
  return mk_bitextract(subst->mngr, t, idx);
}


/*
 * Power products
 */
static term_t subst_pprod(term_subst_t *subst, pprod_t *p, type_t tau) {
  term_t *a;
  term_t result;
  uint32_t i, n, nbits;

  n = p->len;
  a = alloc_istack_array(&subst->stack, n);

  /*
   * p is t_0^e_0 ... t_{n-1}^e_{n-1}
   * compute a[i] = subst(t_i), stop if a[i] is zero
   */
  for (i=0; i<n; i++) {
    a[i] = get_subst(subst, p->prod[i].var);
    if (term_is_zero(subst->terms, a[i])) {
      // the result is zero
      result = a[i];
      goto done;
    }
  }

  /*
   * Check for overflow
   */
  if (pprod_degree_overflows(subst->terms, p, n, a)) {
    longjmp(subst->env, -1); // raise an exception
  }

  /*
   * build the term a[0] ^ e_0 ... a[n-1]^ e_{n-1}
   */
  nbits = bv_type_size(subst->terms->types, tau);
  if (nbits <= 64) {
    result = bvarith64_pprod(subst->mngr, p, n, a, nbits);
  } else {
    result = bvarith_pprod(subst->mngr, p, n, a, nbits);
  }

 done:
  free_istack_array(&subst->stack, a);

  return result;
}



/*
 * Bitvector polynomial: 64bit coefficients
 */
static term_t subst_bvpoly64(term_subst_t *subst, bvpoly64_t *p) {
  term_t *a;
  term_t result;
  uint32_t i, n;

  n = p->nterms;
  a = alloc_istack_array(&subst->stack, n);

  // skip the constant term if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[i] = const_idx;
    i ++;
  }

  // rest of the terms in p
  while (i < n) {
    a[i] = get_subst(subst, p->mono[i].var);
    i ++;
  }

  // build the polynomial
  result = build_bvarith64_poly(subst->mngr, p, n, a);

  free_istack_array(&subst->stack, a);

  return result;
}


/*
 * Bitvector polynomial: more than 64bits
 */
static term_t subst_bvpoly(term_subst_t *subst, bvpoly_t *p) {
  term_t *a;
  term_t result;
  uint32_t i, n;

  n = p->nterms;
  a = alloc_istack_array(&subst->stack, n);

  // skip the constant term if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[i] = const_idx;
    i ++;
  }

  // rest of the terms in p
  while (i < n) {
    a[i] = get_subst(subst, p->mono[i].var);
    i ++;
  }

  // build the polynomial
  result = build_bvarith_poly(subst->mngr, p, n, a);

  free_istack_array(&subst->stack, a);

  return result;
}



/*
 * Core function: recursively compute subst for a composite term t
 * - t has positive polarity
 * - t is a valid term in the term table
 * - t is a composite term
 */
static term_t subst_composite(term_subst_t *subst, term_t t) {
  term_table_t *terms;
  term_t result;

  terms = subst->terms;
  assert(good_term(terms, t) && is_pos_term(t));

  switch (term_kind(terms, t)) {
  case ITE_TERM:
    result = subst_ite(subst, ite_term_desc(terms, t));
    break;

  case EQ_TERM:
    result = subst_eq(subst, eq_term_desc(terms, t));
    break;

  case DISTINCT_TERM:
    result = subst_distinct(subst, distinct_term_desc(terms, t));
    break;

  case OR_TERM:
    result = subst_or(subst, or_term_desc(terms, t));
    break;

  case XOR_TERM:
    result = subst_xor(subst, xor_term_desc(terms, t));
    break;

  case BV_ARRAY:
    result = subst_bvarray(subst, bvarray_term_desc(terms, t));
    break;

  case BV_DIV:
    result = subst_bvdiv(subst, bvdiv_term_desc(terms, t));
    break;

  case BV_REM:
    result = subst_bvrem(subst, bvrem_term_desc(terms, t));
    break;

  case BV_SDIV:
    result = subst_bvsdiv(subst, bvsdiv_term_desc(terms, t));
    break;

  case BV_SREM:
    result = subst_bvsrem(subst, bvsrem_term_desc(terms, t));
    break;

  case BV_SMOD:
    result = subst_bvsmod(subst, bvsmod_term_desc(terms, t));
    break;

  case BV_SHL:
    result = subst_bvshl(subst, bvshl_term_desc(terms, t));
    break;

  case BV_LSHR:
    result = subst_bvlshr(subst, bvlshr_term_desc(terms, t));
    break;

  case BV_ASHR:
    result = subst_bvashr(subst, bvashr_term_desc(terms, t));
    break;

  case BV_EQ_ATOM:
    result = subst_bveq(subst, bveq_atom_desc(terms, t));
    break;

  case BV_GE_ATOM:
    result = subst_bvge(subst, bvge_atom_desc(terms, t));
    break;

  case BV_SGE_ATOM:
    result = subst_bvsge(subst, bvsge_atom_desc(terms, t));
    break;

  case BIT_TERM:
    result = subst_bit_select(subst, bit_term_desc(terms, t));
    break;

  case POWER_PRODUCT:
    result = subst_pprod(subst, pprod_term_desc(terms, t), term_type(terms, t));
    break;

  case BV64_POLY:
    result = subst_bvpoly64(subst, bvpoly64_term_desc(terms, t));
    break;

  case BV_POLY:
    result = subst_bvpoly(subst, bvpoly_term_desc(terms, t));
    break;

  default:
    // error: invalid term_kind or not a composite
    longjmp(subst->env, -2);
    break;
  }

  return result;
}


/*
 * Main substitution function:
 * - if t is atomic and constant return t
 * - if t is a variable, lookup what's mapped to t in subst
 * - otherwise t is composite:
 *   if t is ground, return t
 *   if t is not ground, check the cache; if subst(t) is not
 *   in the cache recursively compute it and store that in the cache.
 */
static term_t get_subst(term_subst_t *subst, term_t t) {
  term_table_t *terms;
  uint32_t polarity;
  term_t result;

  terms = subst->terms;
  assert(good_term(terms, t));

  polarity = polarity_of(t);
  t = unsigned_term(t);

  switch (term_kind(terms, t)) {
  case CONSTANT_TERM:
  case BV64_CONSTANT:
  case BV_CONSTANT:
    result = t;
    break;

  case UNINTERPRETED_TERM:
    result = get_subst_of_unint(subst, t);
    break;

  default:
    /*
     * Composite term
     */
    result = get_cached_subst(subst, t);
    if (result < 0) {
      assert(result == NULL_TERM);
      result = subst_composite(subst, t);
      cache_subst_result(subst, t, result);
    }
    break;
  }

  assert(good_term(terms, result));

  return result ^ polarity;
}



/*
 * Apply the substitution to term t
 * - t must be a valid term in the subst's term manager
 * - return the resulting term
 *
 * Error codes:
 * - return -1 if the result can't be constructed
 *   (because of a degree overflow).
 * - return -2 if something else goes wrong
 */
term_t apply_term_subst(term_subst_t *subst, term_t t) {
  term_t result;
  int code;

  code = setjmp(subst->env);
  if (code == 0) {
    result = get_subst(subst, t);
  } else {
    // Error code
    assert(code == -1 || code == -2);
    result = (term_t) code;

    // Cleanup
    reset_istack(&subst->stack);
  }

  return result;
}



