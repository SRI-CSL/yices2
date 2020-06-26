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
 * UTILITIES FOR SIMPLIFYING TERMS
 */


#include <assert.h>

#include "terms/bv64_constants.h"
#include "terms/term_utils.h"
#include "utils/int_array_sort.h"
#include "utils/int_hash_sets.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"
#include "utils/prng.h"

#if 0

#include <stdio.h>
#include <inttypes.h>
#include "io/term_printer.h"

static void print_finite_domain(FILE *f, term_table_t *tbl, finite_domain_t *d) {
  uint32_t i, n;

  n = d->nelems;
  fputs("[", f);
  for (i=0; i<n; i++) {
    if (i > 0) fputs(" ", f);
    print_term(f, tbl, d->data[i]);
  }
  fputs("]", f);
}
#endif



/********************
 *  FINITE DOMAINS  *
 *******************/

/*
 * Build a domain descriptor that contains a[0 ... n-1]
 */
static finite_domain_t *make_finite_domain(term_t *a, uint32_t n) {
  finite_domain_t *tmp;
  uint32_t i;

  assert(n <= MAX_FINITE_DOMAIN_SIZE);
  tmp = (finite_domain_t *) safe_malloc(sizeof(finite_domain_t) + n * sizeof(term_t));
  tmp->nelems = n;
  for (i=0; i<n; i++) {
    tmp->data[i] = a[i];
  }

  return tmp;
}


/*
 * Add all elements of dom that are not in cache into vector v
 * - also store them in the cache
 */
static void add_domain(int_hset_t *cache, ivector_t *v, finite_domain_t *dom) {
  uint32_t i, n;
  term_t t;

  n = dom->nelems;
  for (i=0; i<n; i++) {
    t = dom->data[i];
    if (int_hset_add(cache, t)) {
      ivector_push(v, t);
    }
  }
}


/*
 * Recursively collect all constant terms reachable from t
 * - add all terms visited to hset
 * - add all constants to vector v
 */
static void collect_finite_domain(term_table_t *tbl, int_hset_t *cache, ivector_t *v, term_t t) {
  special_term_t *d;

  if (int_hset_add(cache, t)) {
    // t not visited yet
    if (term_kind(tbl, t) == ITE_SPECIAL) {
      d = ite_special_desc(tbl, t);
      if (d->extra != NULL) {
        add_domain(cache, v, d->extra);
      } else {
        collect_finite_domain(tbl, cache, v, d->body.arg[1]);
        collect_finite_domain(tbl, cache, v, d->body.arg[2]);
      }
    } else {
      // t must be a constant, not already in v
      assert(is_const_term(tbl, t));
      ivector_push(v, t);
    }
  }
}


/*
 * Build the domain for (ite c t1 t2)
 * - d must be the composite descriptor for (ite c t1 t2)
 */
static finite_domain_t *build_ite_finite_domain(term_table_t *tbl, composite_term_t *d) {
  int_hset_t cache;
  ivector_t buffer;
  finite_domain_t *dom;

  assert(d->arity == 3);

  init_int_hset(&cache, 32);
  init_ivector(&buffer, 20);

  collect_finite_domain(tbl, &cache, &buffer, d->arg[1]);  // then part
  collect_finite_domain(tbl, &cache, &buffer, d->arg[2]);  // else part

  int_array_sort(buffer.data, buffer.size);
  dom = make_finite_domain(buffer.data, buffer.size);

  delete_ivector(&buffer);
  delete_int_hset(&cache);

  return dom;
}


/*
 * Get the finite domain of term t
 */
finite_domain_t *special_ite_get_finite_domain(term_table_t *tbl, term_t t) {
  special_term_t *d;

  d = ite_special_desc(tbl, t);
  if (d->extra == NULL) {
    d->extra = build_ite_finite_domain(tbl, &d->body);
  }
  return d->extra;
}



/*
 * Check whether u belongs to the finite domain of term t
 * - t must be a special if-then-else
 */
bool term_is_in_finite_domain(term_table_t *tbl, term_t t, term_t u) {
  finite_domain_t *dom;
  uint32_t l, h, k;

  dom = special_ite_get_finite_domain(tbl, t);
  assert(dom->nelems >= 2);

  // binary search
  l = 0;
  h = dom->nelems;
  for (;;) {
    k = (l + h)/2; // no overflow possible since l+h < MAX_FINITE_DOMAIN_SIZE
    assert(l <= k && k < h && h <= dom->nelems);
    if (k == l) break;
    if (dom->data[k] > u) {
      h = k;
    } else {
      l = k;
    }
  }

  assert(l == k && k+1 == h);

  return dom->data[k] == u;
}



/*
 * Check whether two finite domains are disjoint.
 */
static bool disjoint_finite_domains(finite_domain_t *d1, finite_domain_t *d2) {
  uint32_t i1, i2, n1, n2;
  term_t t1, t2;

  assert(d1->nelems > 0 && d2->nelems > 0);

  n1 = d1->nelems;
  n2 = d2->nelems;
  i1 = 0;
  i2 = 0;
  t1 = d1->data[0];
  t2 = d2->data[0];
  for (;;) {
    if (t1 == t2) return false;
    if (t1 < t2) {
      i1 ++;
      if (i1 == n1) break;
      t1 = d1->data[i1];
    } else {
      i2 ++;
      if (i2 == n2) break;
      t2 = d2->data[i2];
    }
  }

  return true;
}



/*
 * Check whether t and u have disjoint finite domains
 * - both t and u must be special if-then-else
 * - the domains of t and u are computed if needed.
 */
bool terms_have_disjoint_finite_domains(term_table_t *tbl, term_t t, term_t u) {
  finite_domain_t *d1, *d2;

  d1 = special_ite_get_finite_domain(tbl, t);
  d2 = special_ite_get_finite_domain(tbl, u);
  return disjoint_finite_domains(d1, d2);
}



/*
 * FINITE RATIONAL DOMAIN
 */

/*
 * Check whether all elements in domain d are >= 0
 * - d must be an arithmetic domain (i.e., all elements in d are rational constants)
 */
static bool finite_domain_is_nonneg(term_table_t *tbl, finite_domain_t *d) {
  uint32_t i, n;
  term_t t;

  n = d->nelems;
  for (i=0; i<n; i++) {
    t = d->data[i];
    if (q_is_neg(rational_term_desc(tbl, t))) {
      return false;
    }
  }

  return true;
}


/*
 * Check whether all elements in domain d are <= 0
 * - d must be an arithmetic domain (i.e., all elements in d are rational constants)
 */
static bool finite_domain_is_nonpos(term_table_t *tbl, finite_domain_t *d) {
  uint32_t i, n;
  term_t t;

  n = d->nelems;
  for (i=0; i<n; i++) {
    t = d->data[i];
    if (q_is_pos(rational_term_desc(tbl, t))) {
      return false;
    }
  }

  return true;
}


/*
 * Check whether all elements in domain d are negative
 * - d must be an arithmetic domain
 */
static bool finite_domain_is_neg(term_table_t *tbl, finite_domain_t *d) {
  uint32_t i, n;
  term_t t;

  n = d->nelems;
  for (i=0; i<n; i++) {
    t = d->data[i];
    if (q_is_nonneg(rational_term_desc(tbl, t))) {
      return false;
    }
  }

  return true;
}


/*
 * Check whether all elements in domain d are non-integer
 * - d must be an arithmetic domain
 */
static bool finite_domain_has_no_integers(term_table_t *tbl, finite_domain_t *d) {
  uint32_t i, n;
  term_t t;

  n = d->nelems;
  for (i=0; i<n; i++) {
    t = d->data[i];
    if (q_is_integer(rational_term_desc(tbl, t))) {
      return false;
    }
  }

  return true;
}


/*
 * Check whether all elements in t's domain are non-negative
 * - t must be a special if-then-else of arithmetic type
 * - the domain of t is computed if required
 */
bool term_has_nonneg_finite_domain(term_table_t *tbl, term_t t) {
  finite_domain_t *d;

  d = special_ite_get_finite_domain(tbl, t);
  return finite_domain_is_nonneg(tbl, d);
}


/*
 * Check whether all elements in t's domain are non-positive
 * - t must be a special if-then-else of arithmetic type
 * - the domain of t is computed if required
 */
bool term_has_nonpos_finite_domain(term_table_t *tbl, term_t t) {
  finite_domain_t *d;

  d = special_ite_get_finite_domain(tbl, t);
  return finite_domain_is_nonpos(tbl, d);
}


/*
 * Check whether all elements in t's domain are negative
 * - t must be a special if-then-else term of arithmetic type
 * - the domain of t is computed if required
 */
bool term_has_negative_finite_domain(term_table_t *tbl, term_t t) {
  finite_domain_t *d;

  d = special_ite_get_finite_domain(tbl, t);
  return finite_domain_is_neg(tbl, d);
}


/*
 * Check whether all elements in t's domain are non-integer
 */
bool term_has_non_integer_finite_domain(term_table_t *tbl, term_t t) {
  finite_domain_t *d;

  d = special_ite_get_finite_domain(tbl, t);
  return finite_domain_has_no_integers(tbl, d);
}


/*
 * Check whether t < u
 * - both must be arithmetic constants (rationals)
 */
static bool arith_constant_lt(term_table_t *tbl, term_t t, term_t u) {
  return q_lt(rational_term_desc(tbl, t), rational_term_desc(tbl, u));
}

/*
 * Compute the lower and upper bounds on domain d
 * - d must be a non-empty arithmetic domain
 * - the lower bound is stored in *lb
 * - the upper bound is stored in *ub
 */
static void finite_domain_bounds(term_table_t *tbl, finite_domain_t *d, term_t *lb, term_t *ub) {
  uint32_t i, n;
  term_t t, min, max;

  n = d->nelems;
  assert(n > 0);
  min = d->data[0];
  max = d->data[0];
  for (i=1; i<n; i++) {
    t = d->data[i];
    if (arith_constant_lt(tbl, t, min)) {
      min = t;
    } else if (arith_constant_lt(tbl, max, t)) {
      max = t;
    }
  }

  *lb = min;
  *ub = max;
}


/*
 * Compute the lower and upper bound for term t
 * - t must be a special if-then-else term of arithmetic type
 * - the domain is computed if required
 * - the lower bound is stored in *lb and the upper bound is stored in *ub
 */
void term_finite_domain_bounds(term_table_t *tbl, term_t t, term_t *lb, term_t *ub) {
  finite_domain_t *d;

  d = special_ite_get_finite_domain(tbl, t);

#if 0
  printf("finite domain for term %"PRId32"\n", t);
  print_finite_domain(stdout, tbl, d);
  printf("\n");
#endif

  finite_domain_bounds(tbl, d, lb, ub);
}



/***********************************
 *  OPERATIONS ON BIT ARRAY TERMS  *
 **********************************/

/*
 * Upper/lower bound on a bitarray interpreted as an unsigned integer.
 *   a = a[0] + 2 a[1] + ... + 2^(n-1) a[n-1], with 0 <= a[i] <= 1
 * upper bound: replace a[i] by 1 if a[i] != 0
 * lower bound: replace a[i] by 0 if a[i] != 1
 */
static void bitarray_upper_bound_unsigned(composite_term_t *a, bvconstant_t *c) {
  uint32_t i, n;

  assert(a->arity > 0);

  n = a->arity;
  bvconstant_set_all_one(c, n); // c := 0b1...1 (n bits)
  for (i=0; i<n; i++) {
    if (a->arg[i] == false_term) {
      bvconst_clr_bit(c->data, i);
    }
  }
}

static void bitarray_lower_bound_unsigned(composite_term_t *a, bvconstant_t *c) {
  uint32_t i, n;

  assert(a->arity > 0);

  n = a->arity;
  bvconstant_set_all_zero(c, n); // c := 0b0...0 (n bits)
  for (i=0; i<n; i++) {
    if (a->arg[i] == true_term) {
      bvconst_set_bit(c->data, i);
    }
  }
}


/*
 * Find the number significant bits of a (in 2s complement)
 * - returns m if a is the sign-extension of a smaller b of m bits
 *   or n otherwise
 * - a is an array of n Boolean terms
 * - a[n-1] is the sign bit
 * - this searches for the largest m <= n such that a[m-1] is not equal to a[n-1].
 */
static uint32_t bitarray_significant_bits(composite_term_t *a) {
  uint32_t n;
  term_t sign;

  assert(a->arity > 0);

  n = a->arity - 1;
  sign = a->arg[n]; // sign bit
  while (n > 0) {
    if (a->arg[n - 1] != sign) break;
    n --;
  }
  return n + 1;
}


/*
 * Upper/lower bound on a bitarray interpreted as a signed integer.
 * - a is an array of n bits.
 * - Let m be the number of significant bits in a, then we have
 *   1 <= m <= n
 *   bits a[m-1] .... a[n-1] are all equal (sign extension)
 *   a = a[0] + 2 a[1] + ... + 2^(m-2) a[m-2] - 2^(m-1) a[m-1]
 *
 * upper bound:
 *   for i=0 to m-2, replace a[i] by 1 if a[i] != 0
 *   for i=m-1 to n-1, replace a[i] by 0 unless a[i] = 1.
 *
 * lower bound:
 *   for i=0 to m-2, replace a[i] by 0 if a[i] != 1
 *   for i=m-1 to n-1, replace a[i] by 1 unless a[i] = 0.
 */
static void bitarray_upper_bound_signed(composite_term_t *a, bvconstant_t *c) {
  uint32_t i, n, m;

  assert(a->arity > 0);

  n = a->arity;
  bvconstant_set_all_one(c, n);

  m = bitarray_significant_bits(a);
  assert(0 < m && m <= n);

  for (i=0; i<m-1; i++) {
    if (a->arg[i] == false_term) {
      bvconst_clr_bit(c->data, i);
    }
  }

  // all bits from a->arg[i] to a->arg[n-1] are the same
  if (a->arg[i] != true_term) {
    while (i < n) {
      bvconst_clr_bit(c->data, i);
      i ++;
    }
  }
}


static void bitarray_lower_bound_signed(composite_term_t *a, bvconstant_t *c) {
  uint32_t i, n, m;

  assert(a->arity > 0);

  n = a->arity;
  bvconstant_set_all_zero(c, n);

  m = bitarray_significant_bits(a);
  assert(0 < m && m <= n);

  for (i=0; i<m-1; i++) {
    if (a->arg[i] == true_term) {
      bvconst_set_bit(c->data, i);
    }
  }

  // all bits from a->arg[i] to a->arg[n-1] are the same
  if (a->arg[i] != false_term) {
    while (i < n) {
      bvconst_set_bit(c->data, i);
      i ++;
    }
  }
}




/*
 * BOUNDS FOR ARRAYS OF 1 TO 64BITS
 */

/*
 * Upper/lower bound on a bitarray interpreted as an unsigned integer.
 *   a = a[0] + 2 a[1] + ... + 2^(n-1) a[n-1], with 0 <= a[i] <= 1
 * upper bound: replace a[i] by 1 if a[i] != 0
 * lower bound: replace a[i] by 0 if a[i] != 1
 */
static uint64_t bitarray_upper_bound_unsigned64(composite_term_t *a) {
  uint64_t c;
  uint32_t i, n;

  assert(0 < a->arity && a->arity <= 64);

  n = a->arity;
  c = mask64(n); // c = 0001...1 (n lower bits set)
  for (i=0; i<n; i++) {
    if (a->arg[i] == false_term) {
      c = clr_bit64(c, i);
    }
  }

  assert(c == norm64(c, n));

  return c;
}

static uint64_t bitarray_lower_bound_unsigned64(composite_term_t *a) {
  uint64_t c;
  uint32_t i, n;

  assert(0 < a->arity && a->arity <= 64);

  n = a->arity;
  c = 0;
  for (i=0; i<n; i++) {
    if (a->arg[i] == true_term) {
      c = set_bit64(c, i);
    }
  }

  assert(c == norm64(c, n));

  return c;
}



#if 0

// NOT USED ANYMORE

/*
 * Upper/lower bound on a bitarray interpreted as a signed integer.
 *   a = a[0] + 2 a[1] + ... + 2^(n-2) a[n-2] - 2^(n-1) a[m-1]
 *   where m = number of significant bits in a.
 *
 * upper bound:
 *   for i=0 to m-2, replace a[i] by 1 if a[i] != 0
 *   for i=m-1 to n-1, replace a[i] by 0 unless a[i] = 1.
 *
 * lower bound:
 *   for i=0 to m-2, replace a[i] by 0 if a[i] != 1
 *   for i=m-1 to n-1, replace a[i] by 1 unless a[i] = 0.
 */
static uint64_t bitarray_upper_bound_signed64(composite_term_t *a) {
  uint64_t c;
  uint32_t i, n, m;

  assert(0 < a->arity && a->arity <= 64);

  n = a->arity;
  c = mask64(n); // c = 0001...1

  m = bitarray_significant_bits(a);
  assert(0 < m && m <= n);

  for (i=0; i<m-1; i++) {
    if (a->arg[i] == false_term) {
      c = clr_bit64(c, i);
    }
  }

  // i is equal to m-1
  // All bits from a->arg[m-1] to a->arg[n-1] are the same
  if (a->arg[i] != true_term) {
    while (i < n) {
      c = clr_bit64(c, i);
      i ++;
    }
  }

  assert(c == norm64(c, n));

  return c;
}


static uint64_t bitarray_lower_bound_signed64(composite_term_t *a) {
  uint64_t c;
  uint32_t i, n, m;

  assert(0 < a->arity && a->arity <= 64);

  n = a->arity;
  c = 0;

  m = bitarray_significant_bits(a);
  assert(0 < m && m <= n);

  for (i=0; i<m-1; i++) {
    if (a->arg[i] == true_term) {
      c = set_bit64(c, i);
    }
  }

  // i is equal to m-1.
  // All bits from a->arg[m-1] to a->arg[n-1] are the same
  if (a->arg[i] != false_term) {
    while (i < n) {
      c = set_bit64(c, i);
      i ++;
    }
  }

  assert(c == norm64(c, n));


  return c;
}

#endif


/*
 * DISEQUALITY CHECKS
 */

/*
 * Disequality check between two bit arrays
 * - a and b must have the same arity
 * - all components must be boolean
 *
 * TODO?: improve this.
 * - we could try to see that (l l) can't be equal to (u (not u))
 */
static bool disequal_bitarrays(composite_term_t *a, composite_term_t *b) {
  uint32_t i, n;

  assert(a->arity == b->arity);

  n = a->arity;
  for (i=0; i<n; i++) {
    if (opposite_bool_terms(a->arg[i], b->arg[i])) return true;
  }

  return false;
}


/*
 * Disequality check between bit array a and small constant c
 * - both must have the same bit size
 */
static bool disequal_bitarray_bvconst64(composite_term_t *a, bvconst64_term_t *c) {
  uint32_t i, n;

  assert(a->arity == c->bitsize && 0 < a->arity && a->arity <= 64);

  n = a->arity;
  for (i=0; i<n; i++) {
    if (index_of(a->arg[i]) == bool_const) {
      assert(a->arg[i] == true_term || a->arg[i] == false_term);
      if (a->arg[i] != bool2term(tst_bit64(c->value, i))) {
        return true;
      }
    }
  }

  return false;
}


/*
 * Disequality check between bit array a and bv-constant c
 * - both must have the same bit size
 */
static bool disequal_bitarray_bvconst(composite_term_t *a, bvconst_term_t *c) {
  uint32_t i, n;

  assert(a->arity == c->bitsize && 64 < a->arity);

  n = a->arity;
  for (i=0; i<n; i++) {
    if (index_of(a->arg[i]) == bool_const) {
      assert(a->arg[i] == true_term || a->arg[i] == false_term);
      if (a->arg[i] != bool2term(bvconst_tst_bit(c->data, i))) {
        return true;
      }
    }
  }

  return false;
}



/*************************
 *  CHECK NON-INTEGERS   *
 ************************/

/*
 * Check whether p is of the form constant + sum of integer monomials
 * where the constant is a non-integer rational.
 */
static bool non_integer_polynomial(term_table_t *tbl, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  if (n >= 1 && p->mono[0].var == const_idx && !q_is_integer(&p->mono[0].coeff)) {
    // p has a non-integer constant term
    for (i=1; i<n; i++) {
      if (!is_integer_term(tbl, p->mono[i].var) ||
	  !q_is_integer(&p->mono[i].coeff)) {
	return false; // not an integer monomial
      }
    }
    return true;
  }

  return false;
}

/*
 * Check whether t can't be an integer.
 * This is incomplete.
 * - returns true if t is a non-integer rational
 */
bool arith_term_is_not_integer(term_table_t *tbl, term_t t) {
  assert(is_arithmetic_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case ARITH_CONSTANT:
    return !q_is_integer(rational_term_desc(tbl, t));

  case ARITH_ABS:
    // x not an integer IMPLIES (abs x) not an integer
    return arith_term_is_not_integer(tbl, arith_abs_arg(tbl, t));

  case ARITH_POLY:
    return non_integer_polynomial(tbl, poly_term_desc(tbl, t));

  case ITE_SPECIAL:
    return term_has_non_integer_finite_domain(tbl, t);

  default:
    return false;
  }
}

/*
 * Cheaper form: test whether x is a non-integer constant
 * - incomplete
 */
static bool is_non_integer_term(term_table_t *tbl, term_t x) {
  return term_kind(tbl, x) == ARITH_CONSTANT && !q_is_integer(rational_term_desc(tbl, x));
}




/******************************
 *  CHECKS FOR DISEQUALITIES  *
 *****************************/

/*
 * Base cases:
 * - x and y are both CONSTANT_TERM
 * - x and y are boolean and x = (not y).
 */
static inline bool disequal_constant_terms(term_t x, term_t y) {
  return x != y;
}

static inline bool disequal_boolean_terms(term_t x, term_t y) {
  return opposite_bool_terms(x, y);
}


/*
 * Arithmetic: x and y are both arithmetic terms
 *
 * The conversion of arith_buffer to terms ensures that polynomial
 * terms are not constant and not of the form 1.x for some term x.
 *
 * We deal with simple cases:
 * - x is integer and y is not (or conversely)
 * - both x and y are constant
 * - both x and y are polynomials
 * - x is a polynomial and y is not a constant (i.e., y may occur as a variable in x)
 * - y is a polynomial and x is not a constant
 *
 * TODO? we could do more when (x - y) is a polynomial with integer variables.
 */
bool disequal_arith_terms(term_table_t *tbl, term_t x, term_t y, bool check_ite) {
  term_kind_t kx, ky;

  if (is_integer_term(tbl, x) && is_non_integer_term(tbl, y)) {
    return true;
  }

  if (is_integer_term(tbl, y) && is_non_integer_term(tbl, x)) {
    return true;
  }

  kx = term_kind(tbl, x);
  ky = term_kind(tbl, y);

  if (kx == ARITH_CONSTANT && ky == ARITH_CONSTANT) {
    return x != y; // because of hash consing.
  }

  if (check_ite) {
    if (kx == ARITH_CONSTANT && ky == ITE_SPECIAL) {
      return ! term_is_in_finite_domain(tbl, y, x);
    }

    if (kx == ITE_SPECIAL && ky == ARITH_CONSTANT) {
      return !term_is_in_finite_domain(tbl, x, y);
    }

    if (kx == ITE_SPECIAL && ky == ITE_SPECIAL) {
      return terms_have_disjoint_finite_domains(tbl, x, y);
    }
  }

  if (kx == ARITH_POLY && ky == ARITH_POLY) {
    return disequal_polynomials(poly_term_desc(tbl, x), poly_term_desc(tbl, y));
  }

  if (kx == ARITH_POLY && ky != ARITH_CONSTANT) {
    return polynomial_is_const_plus_var(poly_term_desc(tbl, x), y);
  }

  if (ky == ARITH_POLY && kx != ARITH_CONSTANT) {
    return polynomial_is_const_plus_var(poly_term_desc(tbl, y), x);
  }

  return false;
}




/*
 * Bitvectors: x and y are bitvector terms of 1 to 64 bits
 */
static bool disequal_bv64_terms(term_table_t *tbl, term_t x, term_t y) {
  term_kind_t kx, ky;

  kx = term_kind(tbl, x);
  ky = term_kind(tbl, y);

  if (kx == ky) {
    if (kx == BV64_CONSTANT) {
      return x != y;
    }

    if (kx == BV64_POLY) {
      return disequal_bvpoly64(bvpoly64_term_desc(tbl, x), bvpoly64_term_desc(tbl, y));
    }

    if (kx == BV_ARRAY) {
      return disequal_bitarrays(bvarray_term_desc(tbl, x), bvarray_term_desc(tbl, y));
    }

    if (kx == ITE_SPECIAL) {
      return terms_have_disjoint_finite_domains(tbl, x, y);
    }

  } else {

    if (kx == BV64_CONSTANT && ky == BV_ARRAY) {
      return disequal_bitarray_bvconst64(bvarray_term_desc(tbl, y), bvconst64_term_desc(tbl, x));
    }

    if (ky == BV64_CONSTANT && kx == BV_ARRAY) {
      return disequal_bitarray_bvconst64(bvarray_term_desc(tbl, x), bvconst64_term_desc(tbl, y));
    }

    if (kx == BV64_CONSTANT && ky == ITE_SPECIAL) {
      return !term_is_in_finite_domain(tbl, y, x);
    }

    if (ky == BV64_CONSTANT && kx == ITE_SPECIAL) {
      return !term_is_in_finite_domain(tbl, x, y);
    }

    if (kx == BV64_POLY && ky != BV64_CONSTANT) {
      return bvpoly64_is_const_plus_var(bvpoly64_term_desc(tbl, x), y);
    }

    if (ky == BV64_POLY && kx != BV64_CONSTANT) {
      return bvpoly64_is_const_plus_var(bvpoly64_term_desc(tbl, y), x);
    }

  }

  return false;
}


/*
 * x and y are two bitvectors of more than 64bits
 */
static bool disequal_bv_terms(term_table_t *tbl, term_t x, term_t y) {
  term_kind_t kx, ky;

  kx = term_kind(tbl, x);
  ky = term_kind(tbl, y);

  if (kx == ky) {
    if (kx == BV_CONSTANT) {
      return x != y;
    }

    if (kx == BV_POLY) {
      return disequal_bvpoly(bvpoly_term_desc(tbl, x), bvpoly_term_desc(tbl, y));
    }

    if (kx == BV_ARRAY) {
      return disequal_bitarrays(bvarray_term_desc(tbl, x), bvarray_term_desc(tbl, y));
    }

    if (kx == ITE_SPECIAL) {
      return terms_have_disjoint_finite_domains(tbl, x, y);
    }

  } else {

    if (kx == BV_CONSTANT && ky == BV_ARRAY) {
      return disequal_bitarray_bvconst(bvarray_term_desc(tbl, y), bvconst_term_desc(tbl, x));
    }

    if (ky == BV_CONSTANT && kx == BV_ARRAY) {
      return disequal_bitarray_bvconst(bvarray_term_desc(tbl, x), bvconst_term_desc(tbl, y));
    }

    if (kx == BV_CONSTANT && ky == ITE_SPECIAL) {
      return !term_is_in_finite_domain(tbl, y, x);
    }

    if (ky == BV_CONSTANT && kx == ITE_SPECIAL) {
      return !term_is_in_finite_domain(tbl, x, y);
    }

    if (kx == BV_POLY && ky != BV_CONSTANT) {
      return bvpoly_is_const_plus_var(bvpoly_term_desc(tbl, x), y);
    }

    if (ky == BV_POLY && kx != BV_CONSTANT) {
      return bvpoly_is_const_plus_var(bvpoly_term_desc(tbl, y), x);
    }

  }

  return false;
}


/*
 * Generic form for two bitvector terms x and y
 */
bool disequal_bitvector_terms(term_table_t *tbl, term_t x, term_t y) {
  assert(is_bitvector_term(tbl, x) && is_bitvector_term(tbl, y) &&
         term_bitsize(tbl, x) == term_bitsize(tbl, y));

  if (term_bitsize(tbl, x) <= 64) {
    return disequal_bv64_terms(tbl, x, y);
  } else {
    return disequal_bv_terms(tbl, x, y);
  }
}


/*
 * Tuple terms x and y are trivially distinct if they have components
 * x_i and y_i that are trivially distinct.
 */
static bool disequal_tuple_terms(term_table_t *tbl, term_t x, term_t y, bool check_ite) {
  composite_term_t *tuple_x, *tuple_y;
  uint32_t i, n;

  tuple_x = tuple_term_desc(tbl, x);
  tuple_y = tuple_term_desc(tbl, y);

  n = tuple_x->arity;
  assert(n == tuple_y->arity);
  for (i=0; i<n; i++) {
    if (disequal_terms(tbl, tuple_x->arg[i], tuple_y->arg[i], check_ite)) {
      return true;
    }
  }
  return false;
}


/*
 * (update f x1 ... xn a) is trivially distinct from (update f x1 ... xn b)
 * if a is trivially distinct from b.
 */
static bool disequal_update_terms(term_table_t *tbl, term_t x, term_t y, bool check_ite) {
  composite_term_t *update_x, *update_y;
  int32_t i, n;

  assert(term_type(tbl, x) == term_type(tbl, y));

  update_x = update_term_desc(tbl, x);
  update_y = update_term_desc(tbl, y);

  n = update_x->arity;
  assert(n == update_y->arity && n > 0);
  for (i=0; i<n-1; i++) {
    if (update_x->arg[i] != update_y->arg[i]) return false;
  }

  return disequal_terms(tbl, update_x->arg[i], update_y->arg[i], check_ite);
}


/*
 * Top level check: x and y must be valid terms of compatible types
 */
bool disequal_terms(term_table_t *tbl, term_t x, term_t y, bool check_ite) {
  term_kind_t kind;

  if (is_boolean_term(tbl, x)) {
    assert(is_boolean_term(tbl, y));
    return disequal_boolean_terms(x, y);
  }

  if (is_arithmetic_term(tbl, x)) {
    assert(is_arithmetic_term(tbl, y));
    return disequal_arith_terms(tbl, x, y, check_ite);
  }

  if (is_bitvector_term(tbl, x)) {
    assert(is_bitvector_term(tbl, y) && term_bitsize(tbl, x) == term_bitsize(tbl, y));
    if (term_bitsize(tbl, x) <= 64) {
      return disequal_bv64_terms(tbl, x, y);
    } else {
      return disequal_bv_terms(tbl, x, y);
    }
  }

  kind = term_kind(tbl, x);
  if (kind != term_kind(tbl, y)) return false;

  switch (kind) {
  case CONSTANT_TERM:
    return disequal_constant_terms(x, y);
  case TUPLE_TERM:
    return disequal_tuple_terms(tbl, x, y, check_ite);
  case UPDATE_TERM:
    return disequal_update_terms(tbl, x, y, check_ite);
  default:
    return false;
  }
}



// check whether a[i] cannot be equal to b[i] for one i
bool disequal_term_arrays(term_table_t *tbl, uint32_t n, const term_t *a, const term_t *b, bool check_ite) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (disequal_terms(tbl, a[i], b[i], check_ite)) return true;
  }

  return false;
}

// check whether all elements of a are disequal
// this is expensive: quadratic cost, but should fail quickly on most examples
bool pairwise_disequal_terms(term_table_t *tbl, uint32_t n, const term_t *a, bool check_ite) {
  uint32_t i, j;

  for (i=0; i<n; i++) {
    for (j=i+1; j<n; j++) {
      if (! disequal_terms(tbl, a[i], a[j], check_ite)) return false;
    }
  }

  return true;
}




/********************************
 *  BOUNDS ON ARITHMETIC TERMS  *
 *******************************/

/*
 * Check whether t is non-negative. This is incomplete and
 * deals only with simple cases.
 * - return true if the checks can determine that t >= 0
 * - return false otherwise
 */
bool arith_term_is_nonneg(term_table_t *tbl, term_t t, bool check_ite) {
  assert(is_arithmetic_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case ARITH_CONSTANT:
    return q_is_nonneg(rational_term_desc(tbl, t));

  case ITE_SPECIAL:
    return check_ite && term_has_nonneg_finite_domain(tbl, t);

  case ARITH_POLY:
    return polynomial_is_nonneg(poly_term_desc(tbl, t));

  case ARITH_ABS:
    return true;

  case ARITH_FLOOR:
    // (floor t) >= 0 IFF t >= 0
    return arith_term_is_nonneg(tbl, arith_floor_arg(tbl, t), check_ite);

  case ARITH_CEIL:
    // t>=0 IMPLIES (ceil t) >= 0
    return arith_term_is_nonneg(tbl, arith_ceil_arg(tbl, t), check_ite);

  default:
    return false;
  }
}

/*
 * Check whether t is negative or null. This is incomplete and
 * deals only with simple cases.
 * - return true if the checks can determine that t <= 0
 * - return false otherwise
 */
bool arith_term_is_nonpos(term_table_t *tbl, term_t t, bool check_ite) {
  assert(is_arithmetic_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case ARITH_CONSTANT:
    return q_is_nonpos(rational_term_desc(tbl, t));

  case ITE_SPECIAL:
    return check_ite && term_has_nonpos_finite_domain(tbl, t);

  case ARITH_POLY:
    return polynomial_is_nonpos(poly_term_desc(tbl, t));

  case ARITH_FLOOR:
    // t <= 0 IMPLIES (floor t) <= 0
    return arith_term_is_nonpos(tbl, arith_floor_arg(tbl, t), check_ite);

  case ARITH_CEIL:
    // (ceil t) <= 0 IFF t <= 0
    return arith_term_is_nonpos(tbl, arith_ceil_arg(tbl, t), check_ite);

  default:
    return false;
  }
}


/*
 * Check whether t is negative (incomplete)
 * - return true if the checks succeed and determine that t < 0
 * - return false otherwise
 */
bool arith_term_is_negative(term_table_t *tbl, term_t t, bool check_ite) {
  assert(is_arithmetic_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case ARITH_CONSTANT:
    return q_is_neg(rational_term_desc(tbl, t));

  case ITE_SPECIAL:
    return check_ite && term_has_negative_finite_domain(tbl, t);

  case ARITH_POLY:
    return polynomial_is_neg(poly_term_desc(tbl, t));

  default:
    return false;
  }
}


/*
 * Check whether t is non-zero (incomplete)
 * - return true if the checks succeed and determine that t != 0
 * - return false otherwise
 */
bool arith_term_is_nonzero(term_table_t *tbl, term_t t, bool check_ite) {
  assert(is_arithmetic_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case ARITH_CONSTANT:
    return t != zero_term;

  case ITE_SPECIAL:
    return check_ite && term_has_nonzero_finite_domain(tbl, t);

  case ARITH_POLY:
    return polynomial_is_nonzero(poly_term_desc(tbl, t));

  default:
    return false;
  }
}




/*******************************
 *  BOUNDS ON BITVECTOR TERMS  *
 ******************************/

/*
 * Copy a bitvector constant a into c
 */
static inline void copy_bvconst_term(bvconst_term_t *a, bvconstant_t *c) {
  assert(a->bitsize > 0);
  bvconstant_copy(c, a->bitsize, a->data);
}

static void copy_bvconst64_term(bvconst64_term_t *a, bvconstant_t *c) {
  uint32_t aux[2];


  aux[0] = (uint32_t) a->value; // lower-order word
  aux[1] = (uint32_t) (a->value >> 32); // high order word  (unused if bitsize <= 32)
  bvconstant_copy(c, a->bitsize, aux);
}


/*
 * Upper bound on t, interpreted as an unsigned integer
 * - copy the result in c
 */
void upper_bound_unsigned(term_table_t *tbl, term_t t, bvconstant_t *c) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    copy_bvconst64_term(bvconst64_term_desc(tbl, t), c);
    break;

  case BV_CONSTANT:
    copy_bvconst_term(bvconst_term_desc(tbl, t), c);
    break;

  case BV_ARRAY:
    bitarray_upper_bound_unsigned(bvarray_term_desc(tbl, t), c);
    break;

  default:
    n = term_bitsize(tbl, t);
    bvconstant_set_all_one(c, n);
    break;
  }
}



/*
 * Lower bound on t, interpreted as an unsigned integer
 * - copy the result in c
 */
void lower_bound_unsigned(term_table_t *tbl, term_t t, bvconstant_t *c) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    copy_bvconst64_term(bvconst64_term_desc(tbl, t), c);
    break;

  case BV_CONSTANT:
    copy_bvconst_term(bvconst_term_desc(tbl, t), c);
    break;

  case BV_ARRAY:
    bitarray_lower_bound_unsigned(bvarray_term_desc(tbl, t), c);
    break;

  default:
    n = term_bitsize(tbl, t);
    bvconstant_set_all_zero(c, n);
    break;
  }
}


/*
 * Upper bound on t, interpreted as a signed integer
 * - copy the result in c
 */
void upper_bound_signed(term_table_t *tbl, term_t t, bvconstant_t *c) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    copy_bvconst64_term(bvconst64_term_desc(tbl, t), c);
    break;

  case BV_CONSTANT:
    copy_bvconst_term(bvconst_term_desc(tbl, t), c);
    break;

  case BV_ARRAY:
    bitarray_upper_bound_signed(bvarray_term_desc(tbl, t), c);
    break;

  default:
    n = term_bitsize(tbl, t);
    assert(n > 0);
    bvconstant_set_all_one(c, n);
    bvconst_clr_bit(c->data, n-1); // clear the sign bit
    break;
  }
}


/*
 * Lower bound on t, interpreted as a signed integer
 * - copy the result in c
 */
void lower_bound_signed(term_table_t *tbl, term_t t, bvconstant_t *c) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    copy_bvconst64_term(bvconst64_term_desc(tbl, t), c);
    break;

  case BV_CONSTANT:
    copy_bvconst_term(bvconst_term_desc(tbl, t), c);
    break;

  case BV_ARRAY:
    bitarray_lower_bound_signed(bvarray_term_desc(tbl, t), c);
    break;

  default:
    n = term_bitsize(tbl, t);
    assert(n > 0);
    bvconstant_set_all_zero(c, n);
    bvconst_set_bit(c->data, n-1); // set the sign bit
    break;
  }
}




/*
 * BOUNDS FOR VECTORS OF 1 TO 64 BITS
 */

/*
 * Upper bound on t, interpreted as an unsigned integer
 */
uint64_t upper_bound_unsigned64(term_table_t *tbl, term_t t) {
  uint64_t c;
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    c = bvconst64_term_desc(tbl, t)->value;
    break;

  case BV_ARRAY:
    c = bitarray_upper_bound_unsigned64(bvarray_term_desc(tbl, t));
    break;

  default:
    n = term_bitsize(tbl, t);
    assert(1 <= n && n <= 64);
    c = mask64(n);
    break;
  }

  return c;
}


/*
 * Lower bound on t, interpreted as an unsigned integer
 */
uint64_t lower_bound_unsigned64(term_table_t *tbl, term_t t) {
  uint64_t c;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    c = bvconst64_term_desc(tbl, t)->value;
    break;

  case BV_ARRAY:
    c = bitarray_lower_bound_unsigned64(bvarray_term_desc(tbl, t));
    break;

  default:
    c = 0;
    break;
  }

  return c;
}


/*
 * Upper bound on t, interpreted as a signed integer
 */
uint64_t upper_bound_signed64(term_table_t *tbl, term_t t) {
  bv64_abs_t abs;
  uint64_t c;
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  bv64_abstract_term(tbl, t, &abs);
  n = term_bitsize(tbl, t);
  c = norm64((uint64_t) abs.high, n);

  return c;
}


/*
 * Lower bound on t, interpreted as a signed integer
 */
uint64_t lower_bound_signed64(term_table_t *tbl, term_t t) {
  bv64_abs_t abs;
  uint64_t c;
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  bv64_abstract_term(tbl, t, &abs);
  n = term_bitsize(tbl, t);
  c = norm64((uint64_t) abs.low, n);

  return c;
}


/******************************************************
 *  MINIMAL/MAXIMAL SIGNED/UNSIGNED BITVECTOR VALUES  *
 *****************************************************/

bool bvterm_is_zero(term_table_t *tbl, term_t t) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    return bvconst64_term_desc(tbl, t)->value == 0;

  case BV_CONSTANT:
    n = (term_bitsize(tbl, t) + 31) >> 5; // number of words
    return bvconst_is_zero(bvconst_term_desc(tbl, t)->data, n);

  default:
    return false;
  }
}

bool bvterm_is_minus_one(term_table_t *tbl, term_t t) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst64_is_minus_one(bvconst64_term_desc(tbl, t)->value, n);

  case BV_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst_is_minus_one(bvconst_term_desc(tbl, t)->data, n);

  default:
    return false;
  }
}

bool bvterm_is_min_signed(term_table_t *tbl, term_t t) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst64_term_desc(tbl, t)->value == min_signed64(n);

  case BV_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst_is_min_signed(bvconst_term_desc(tbl, t)->data, n);

  default:
    return false;
  }
}

bool bvterm_is_max_signed(term_table_t *tbl, term_t t) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst64_term_desc(tbl, t)->value == max_signed64(n);

  case BV_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst_is_max_signed(bvconst_term_desc(tbl, t)->data, n);

  default:
    return false;
  }
}







/*****************************************
 *  REWRITING OF BV-ARRAY TO ARITHMETIC  *
 ****************************************/

/*
 * Record to store the result of a scan:
 * - a scan succceeds in an array a[i .... n-1] if a[i...i+k] is
 *   equal to some term x or (bvnot x)
 * The records stores
 * - success/failure
 * - the term x in question
 * - whether the scan found x or (bvnot x)
 * - the number of bits scanned (i.e., k)
 */
typedef struct bvscan_result_s {
  bool success;
  term_t term;
  bool negated;
  uint32_t numbits;
} bvscan_result_t;


/*
 * Check whether t is (bit-extract x 0) or (not (bit-extract x 0))
 * - if so return x otherwise return null_term
 */
static term_t term_is_start_bit(const term_table_t *tbl, term_t t) {
  select_term_t *d;
  term_t x;

  x = NULL_TERM;
  if (term_kind(tbl, t) == BIT_TERM) {
    d = bit_term_desc(tbl, t);
    if (d->idx == 0) {
      x = d->arg;
    }
  }
  return x;
}

/*
 * Check whether t is (bit-extract x i) or (not (bit-extract x i))
 */
static bool term_is_bit_extract(const term_table_t *tbl, term_t t, term_t x, uint32_t i) {
  select_term_t *d;

  if (term_kind(tbl, t) == BIT_TERM) {
    d = bit_term_desc(tbl, t);
    return d->idx == i && d->arg == x;
  }

  return  false;
}

/*
 * Scan a bit-array a[ .... n-1] starting at index i
 * and search for a pattern (bit 0 x) ... (bit j x)
 *               or (not (bit 0 x)) .... (not (bit j x))
 */
static void bvscan(const term_table_t *tbl, bvscan_result_t *result, uint32_t i, uint32_t n, const term_t *a) {
  term_t b0, x;
  uint32_t j;

  assert(i <= n);

  if (i == n) goto failed;

  b0 = a[i];
  x = term_is_start_bit(tbl, b0);
  if (x == NULL_TERM) goto failed;

  assert(term_is_bit_extract(tbl, a[i], x, 0));

  j = 1;
  i ++;
  while (i<n && polarity_of(a[i]) == polarity_of(b0)
	 && term_is_bit_extract(tbl, a[i], x, j)) {
    i ++;
    j ++;
  }

  // success
  result->success = true;
  result->term = x;
  result->negated = is_neg_term(b0);
  result->numbits = j;
  return;

 failed:
  result->success = false;
}


/*
 * Record to store the result of a constant scan
 * - we scan an array of bits a[i ... i+k-1] and try to convert
 *   the bits to a constant value
 * - the record stores the number of bits scanned (i.e., k)
 *   and the value if k>0.
 * - bitsize is the bitsize for the constant
 * - width is the number of words = ceil(bitsize/32)
 * - if bitsize <= 64, the constant is stored in val64
 * - if bitsize > 64, the constant is stored in array val
 *   an array of the right size if allocated if needed
 *
 * To save a call to malloc, we include a buffer of 20 words.
 * This is enough to store a constant of 640 bits or less.
 */
#define BVCONST_SCAN_BUFFER_SIZE 20

typedef struct bvconst_scan_result_s {
  uint32_t bitsize;
  uint32_t width;
  uint32_t numbits; // number of bits scanned
  uint64_t val64;
  uint32_t *val;
  uint32_t buffer[BVCONST_SCAN_BUFFER_SIZE];
} bvconst_scan_result_t;

// Initialize for an n-bit value
static void init_bvconst_scan(bvconst_scan_result_t *result, uint32_t n) {
  result->bitsize = n;
  result->width = (n + 31) >> 5;
  result->numbits = 0;
  result->val64 = 0;
  result->val = NULL;
}

// Allocate memory for the constant if needed, initialize the constant to zero
// and set the val pointer
static void prepare_bvconst_scan(bvconst_scan_result_t *result) {
  uint32_t n;

  n = result->width;
  if (n > 2) {
    assert(result->bitsize > 64);
    if (n <= BVCONST_SCAN_BUFFER_SIZE) {
      result->val = result->buffer;
    } else {
      result->val = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
    }
    bvconst_clear(result->val, n);
  }
}

// Set bit i of the internal constant
static void bvconst_scan_set_bit(bvconst_scan_result_t *result, uint32_t i) {
  assert(i < result->bitsize);

  if (result->bitsize <= 64) {
    result->val64 |= (((uint64_t) 1) << i);
  } else {
    bvconst_set_bit(result->val, i);
  }
}

// Check that the constant is normalized
#ifndef NDEBUG
static bool bvconst_scan_is_normalized(bvconst_scan_result_t *result) {
  if (result->bitsize <= 64) {
    return result->val64 == norm64(result->val64, result->bitsize);
  } else {
    return bvconst_is_normalized(result->val, result->bitsize);
  }
}
#endif

// Free the allocate buffer if needed
static void delete_bvconst_scan(bvconst_scan_result_t *result) {
  if (result->val != NULL && result->width > BVCONST_SCAN_BUFFER_SIZE) {
    safe_free(result->val);
    result->val = NULL;
  }
}


// check whether term t is a boolean constant
static inline bool is_bool_constant(term_t t) {
  return t == false_term || t == true_term;
}

/*
 * Scan bit-array a[ .... n-1] starting at index i
 * - convert a[i .... i+k-1] to a constant and store the result in *result
 */
static void bvscan_for_constant(const term_table_t *tbl, bvconst_scan_result_t *result,
				uint32_t i, uint32_t n, const term_t *a) {
  uint32_t j;

  assert(i < n);

  if (! is_bool_constant(a[i])) {
    result->numbits = 0; // nothing scanned
    return;
  }

  j = 0;
  prepare_bvconst_scan(result);

  do {
    if (a[i] == true_term) bvconst_scan_set_bit(result, j);
    i ++;
    j ++;
  } while (i < n && is_bool_constant(a[i]));

  result->numbits = j;
  assert(bvconst_scan_is_normalized(result));
}



/*
 * Check whether t is equal to x or (bv-not x) for some term x
 * - t must be a bit-vector array (BV_ARRAY)
 * - the function returns true if t is equal to x or (bv-not x)
 *   it returns the term x in *x
 *   if t is equal to x, the negated flag is set to false
 *   if t is equal to (bv-not x), the negated flag is set to true
 * - the function returns false if t is not of the right form and leaves *x and *negated unchanged
 */
bool bvarray_convertible_to_term(term_table_t *tbl, term_t t, term_t *x, bool *negated) {
  composite_term_t *bits;
  bvscan_result_t result;
  uint32_t n;

  assert(term_kind(tbl, t) == BV_ARRAY);
  bits = bvarray_term_desc(tbl, t);
  n = bits->arity;

  bvscan(tbl, &result, 0, n, bits->arg);
  if (result.success &&
      result.numbits == n &&
      term_bitsize(tbl, result.term) == n ) {
    *x = result.term;
    *negated = result.negated;
    return true;
  }

  return false;
}


#if 0
/*
 * Try to convert t to an arithmetic expression
 * - t must be a bv-array term
 * - return true if that succeeds, and store the result in buffer b
 * - otherwise return false and leave b unchanged.
 *
 * We currently just check for the case t = (bvnot x) or t = x.
 * If t is (bvnot x), we store -1 - x in b.
 */
bool convert_bvarray_to_bvarith64(term_table_t *tbl, term_t t, bvarith64_buffer_t *b) {
  composite_term_t *bits;
  bvscan_result_t result;
  pprod_t *pp;
  uint32_t n;

  assert(term_kind(tbl, t) == BV_ARRAY);
  bits = bvarray_term_desc(tbl, t);
  n = bits->arity;
  assert(0 < n && n <= 64);

  bvscan(tbl, &result, 0, n, bits->arg);
  if (result.success &&
      result.numbits == n &&
      term_bitsize(tbl, result.term) == n ) {

    pp = pprod_for_term(tbl, result.term);
    if (result.negated) {
      // t is (bvnot x) = (2^n-1) - x = (-1) - x
      bvarith64_buffer_sub_one(b);
      bvarith64_buffer_sub_pp(b, pp);
    } else {
      // t is x
      bvarith64_buffer_add_pp(b, pp);
    }
    bvarith64_buffer_normalize(b);
    return true;
  }

  return false;
}

bool convert_bvarray_to_bvarith(term_table_t *tbl, term_t t, bvarith_buffer_t *b) {
  composite_term_t *bits;
  bvscan_result_t result;
  pprod_t *pp;
  uint32_t n;

  assert(term_kind(tbl, t) == BV_ARRAY);
  bits = bvarray_term_desc(tbl, t);
  n = bits->arity;
  assert(n > 64);

  bvscan(tbl, &result, 0, n, bits->arg);
  if (result.success &&
      result.numbits == n &&
      term_bitsize(tbl, result.term) == n) {

    pp = pprod_for_term(tbl, result.term);
    if (result.negated) {
      // t is (bvnot x) = (2^n-1) - x = (-1) - x
      bvarith_buffer_sub_one(b);
      bvarith_buffer_sub_pp(b, pp);
    } else {
      // t is x
      bvarith_buffer_add_pp(b, pp);
    }
    bvarith_buffer_normalize(b);
    return true;
  }

  return false;
}
#endif


/*
 * Try to rewrite array a[0 ... n] as c + 2^k * x or c + 2^k * (bvnot x)
 * where x has n bits.
 *
 * - return true if that works
 * - store c and k in cscan
 * - store x/bvnot x in vscan
 */
static bool convert_bvarray(const term_table_t *tbl, bvconst_scan_result_t *cscan,
			    bvscan_result_t *vscan, uint32_t n, const term_t *a) {
  uint32_t k;

  bvscan_for_constant(tbl, cscan, 0, n, a);
  k = cscan->numbits;
  bvscan(tbl, vscan, k, n, a);

  return vscan->success && vscan->numbits + k == n
    && term_bitsize(tbl, vscan->term) == n;
}


/*
 * Add c + 2^k * x or c + 2^k * (bvnot x) to b
 * - k is given by cscan->numbits
 * - c is stored in cscan->val64 or csan->val
 * - c is smaller than 2^k
 */
static void add_decomp_to_buffer(bvpoly_buffer_t *b, bvconst_scan_result_t *cscan, term_t x, bool negated) {
  uint32_t k, n;
  uint64_t a;

  assert(cscan->bitsize == bvpoly_buffer_bitsize(b));

  n = cscan->bitsize;
  k = cscan->numbits;
  assert(k < n);

  if (k == 0) {
    // no constant and 2^k is 1
    if (negated) {
      // add (bvnot x) = -1 - x
      bvpoly_buffer_sub_one(b);
      bvpoly_buffer_sub_var(b, x);
    } else {
      // add x
      bvpoly_buffer_add_var(b, x);
    }
  } else if (n <= 64) {
    // 64-bit constant stored in cscan->val64
    bvpoly_buffer_add_const64(b, cscan->val64);

    a = ((uint64_t) 1) << k; // 2^k
    if (negated) {
      // add 2^k * (bvnot x) = - 2^k - 2^k * x
      bvpoly_buffer_sub_const64(b, a);
      bvpoly_buffer_sub_mono64(b, x, a);
    } else {
      // add 2^ k * x
      bvpoly_buffer_add_mono64(b, x, a);
    }

  } else {
    // n-bit constant stored in cscan->val
    bvpoly_buffer_add_constant(b, cscan->val);

    // we store 2^k in cscan->val since it has the right size
    bvconst_clear(cscan->val, cscan->width);
    bvconst_set_bit(cscan->val, k);

    if (negated) {
      // add 2^k * (bvnot x)
      bvpoly_buffer_sub_constant(b, cscan->val);
      bvpoly_buffer_sub_monomial(b, x, cscan->val);
    } else {
      // add 2^k * x
      bvpoly_buffer_add_monomial(b, x, cscan->val);
    }
  }
}


/*
 * Subtract c + 2^k * x or c + 2^k * (bvnot x) from  b
 * - k is given by cscan->numbits
 * - c is stored in cscan->val64 or csan->val
 * - c is smaller than 2^k
 */
static void sub_decomp_from_buffer(bvpoly_buffer_t *b, bvconst_scan_result_t *cscan, term_t x, bool negated) {
  uint32_t k, n;
  uint64_t a;

  assert(cscan->bitsize == bvpoly_buffer_bitsize(b));

  n = cscan->bitsize;
  k = cscan->numbits;
  assert(k < n);

  if (k == 0) {
    // no constant and 2^k is 1
    if (negated) {
      // subtract (bvnot x) = -1 - x
      bvpoly_buffer_add_one(b);
      bvpoly_buffer_add_var(b, x);
    } else {
      // subtract x
      bvpoly_buffer_sub_var(b, x);
    }
  } else if (n <= 64) {
    // 64-bit constant stored in cscan->val64
    bvpoly_buffer_sub_const64(b, cscan->val64);

    a = ((uint64_t) 1) << k; // 2^k
    if (negated) {
      // subtract 2^k * (bvnot x) = - 2^k - 2^k * x
      bvpoly_buffer_add_const64(b, a);
      bvpoly_buffer_add_mono64(b, x, a);
    } else {
      // subtract 2^ k * x
      bvpoly_buffer_sub_mono64(b, x, a);
    }

  } else {
    // n-bit constant stored in cscan->val
    bvpoly_buffer_sub_constant(b, cscan->val);

    // we store 2^k in cscan->val since it has the right size
    bvconst_clear(cscan->val, cscan->width);
    bvconst_set_bit(cscan->val, k);

    if (negated) {
      // subtract 2^k * (bvnot x)
      bvpoly_buffer_add_constant(b, cscan->val);
      bvpoly_buffer_add_monomial(b, x, cscan->val);
    } else {
      // subtract 2^k * x
      bvpoly_buffer_sub_monomial(b, x, cscan->val);
    }
  }
}


/*
 * Add bit-array term t to buffer b
 * - try to convert t to an arithmetic expression
 */
static void add_bvarray_to_buffer(const term_table_t *tbl, term_t t, bvpoly_buffer_t *b) {
  composite_term_t *bits;
  bvconst_scan_result_t cscan;
  bvscan_result_t vscan;
  uint32_t n;
  term_t x;

  assert(term_kind(tbl, t) == BV_ARRAY);

  bits = bvarray_term_desc(tbl, t);
  n = bits->arity;
  assert(0 < n && n == bvpoly_buffer_bitsize(b));

  init_bvconst_scan(&cscan, n);
  if (convert_bvarray(tbl, &cscan, &vscan, n, bits->arg)) {
    // success: t is c + 2^k * x or c + 2^k * (bvnot x)
    // k is stored in cscan.numbits
    // c is stored in cscan.val64 or cscan.val
    x = vscan.term;
    assert(term_bitsize(tbl, x) == n);
    add_decomp_to_buffer(b, &cscan, x, vscan.negated);

  } else {
    // can't rewrite t to an arithmetic expression
    bvpoly_buffer_add_var(b, t);
  }

  delete_bvconst_scan(&cscan);
}


/*
 * Subtract bit-array term t from buffer b
 * - try to convert t to an arithmetic expression
 */
static void sub_bvarray_from_buffer(const term_table_t *tbl, term_t t, bvpoly_buffer_t *b) {
  composite_term_t *bits;
  bvconst_scan_result_t cscan;
  bvscan_result_t vscan;
  uint32_t n;
  term_t x;

  assert(term_kind(tbl, t) == BV_ARRAY);

  bits = bvarray_term_desc(tbl, t);
  n = bits->arity;
  assert(0 < n && n == bvpoly_buffer_bitsize(b));

  init_bvconst_scan(&cscan, n);
  if (convert_bvarray(tbl, &cscan, &vscan, n, bits->arg)) {
    // success: t is c + 2^k * x or c + 2^k * (bvnot x)
    // k is stored in cscan.numbits
    // c is stored in cscan.val64 or cscan.val
    x = vscan.term;
    assert(term_bitsize(tbl, x) == n);
    sub_decomp_from_buffer(b, &cscan, x, vscan.negated);

  } else {
    // can't rewrite t to an arithmetic expression
    bvpoly_buffer_sub_var(b, t);
  }

  delete_bvconst_scan(&cscan);
}


/*
 * Add term t to buffer b
 * - attempt to convert t to an arithmetic expression
 */
void add_bvterm_to_buffer(term_table_t *tbl, term_t t, bvpoly_buffer_t *b) {
  assert(is_bitvector_term(tbl, t) && term_bitsize(tbl, t) == bvpoly_buffer_bitsize(b));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    bvpoly_buffer_add_const64(b, bvconst64_term_desc(tbl, t)->value);
    break;

  case BV_CONSTANT:
    bvpoly_buffer_add_constant(b, bvconst_term_desc(tbl, t)->data);
    break;

  case BV64_POLY:
    bvpoly_buffer_add_poly64(b, bvpoly64_term_desc(tbl, t));
    break;

  case BV_POLY:
    bvpoly_buffer_add_poly(b, bvpoly_term_desc(tbl, t));
    break;

  case BV_ARRAY:
    add_bvarray_to_buffer(tbl, t, b);
    break;

  default:
    bvpoly_buffer_add_var(b, t);
    break;
  }

}


/*
 * Subtract t from buffer b
 * - attempt to convert t to an arithemtic expression
 */
void sub_bvterm_from_buffer(term_table_t *tbl, term_t t, bvpoly_buffer_t *b) {
  assert(is_bitvector_term(tbl, t) && term_bitsize(tbl, t) == bvpoly_buffer_bitsize(b));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    bvpoly_buffer_sub_const64(b, bvconst64_term_desc(tbl, t)->value);
    break;

  case BV_CONSTANT:
    bvpoly_buffer_sub_constant(b, bvconst_term_desc(tbl, t)->data);
    break;

  case BV64_POLY:
    bvpoly_buffer_sub_poly64(b, bvpoly64_term_desc(tbl, t));
    break;

  case BV_POLY:
    bvpoly_buffer_sub_poly(b, bvpoly_term_desc(tbl, t));
    break;

  case BV_ARRAY:
    sub_bvarray_from_buffer(tbl, t, b);
    break;

  default:
    bvpoly_buffer_sub_var(b, t);
    break;
  }
}


/*
 * ADD d * t TO A BUFFER: 64bit version
 */

/*
 * Add d * (c + 2^k * x) or d * (c + 2^k * (bvnot x)) to b
 * - numbits <= 64
 * - k is given by cscan->numbits
 * - c is stored in cscan->val64
 * - c is smaller than 2^k
 */
static void addmul_decomp64_to_buffer(bvpoly_buffer_t *b, bvconst_scan_result_t *cscan, term_t x, bool negated, uint64_t d) {
  uint32_t k;
  uint64_t a;

  assert(cscan->bitsize == bvpoly_buffer_bitsize(b) && cscan->bitsize <= 64);

  k = cscan->numbits;
  assert(k < cscan->bitsize);

  if (k == 0) {
    // no constant and 2^k is 1
    if (negated) {
      // add d * (bvnot x) = -d - d * x
      bvpoly_buffer_sub_const64(b, d);
      bvpoly_buffer_sub_mono64(b, x, d);
    } else {
      // add d * x
      bvpoly_buffer_add_mono64(b, x, d);
    }
  } else {
    // c :=  64-bit constant stored in cscan->val64
    // add d * c to buffer b
    bvpoly_buffer_addmul_const64(b, cscan->val64, d);

    // now add d * 2^k * x or d * 2^k * (bvnot x)
    a = d << k; // a = d * 2^k
    if (negated) {
      // add d * (2^k * (bvnot x)) = - d * 2^k - d * 2^k * x = - a - a * x
      bvpoly_buffer_sub_const64(b, a);
      bvpoly_buffer_sub_mono64(b, x, a);
    } else {
      // add d * 2^k * x = a * x
      bvpoly_buffer_add_mono64(b, x, a);
    }
  }
}


/*
 * Add a * bit-array term t to buffer b
 * - try to convert t to an arithmetic expression
 */
static void addmul_bvarray64_to_buffer(const term_table_t *tbl, term_t t, bvpoly_buffer_t *b, uint64_t a) {
  composite_term_t *bits;
  bvconst_scan_result_t cscan;
  bvscan_result_t vscan;
  uint32_t n;
  term_t x;

  assert(term_kind(tbl, t) == BV_ARRAY);

  bits = bvarray_term_desc(tbl, t);
  n = bits->arity;
  assert(0 < n && n == bvpoly_buffer_bitsize(b));

  init_bvconst_scan(&cscan, n);
  if (convert_bvarray(tbl, &cscan, &vscan, n, bits->arg)) {
    // success: t is c + 2^k * x or c + 2^k * (bvnot x)
    // k is stored in cscan.numbits
    // c is stored in cscan.val64
    x = vscan.term;
    assert(term_bitsize(tbl, x) == n);
    addmul_decomp64_to_buffer(b, &cscan, x, vscan.negated, a);

  } else {
    // can't rewrite t to an arithmetic expression
    bvpoly_buffer_add_mono64(b, t, a);
  }

  delete_bvconst_scan(&cscan);
}


/*
 * Add a * t to buffer b
 * - attempt to convert t to an arithmetic expression
 */
void addmul_bvterm64_to_buffer(term_table_t *tbl, term_t t, uint64_t a, bvpoly_buffer_t *b) {
  assert(is_bitvector_term(tbl, t) && term_bitsize(tbl, t) == bvpoly_buffer_bitsize(b));
  assert(term_bitsize(tbl, t) <= 64);

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    bvpoly_buffer_addmul_const64(b, bvconst64_term_desc(tbl, t)->value, a);
    break;

  case BV64_POLY:
    bvpoly_buffer_addmul_poly64(b, bvpoly64_term_desc(tbl, t), a);
    break;

  case BV_ARRAY:
    addmul_bvarray64_to_buffer(tbl, t, b, a);
    break;

  default:
    bvpoly_buffer_add_mono64(b, t, a);
    break;
  }

}

/*
 * Subtract a * t from buffer b
 * - attempt to convert t to an arithemtic expression
 */
void submul_bvterm64_from_buffer(term_table_t *tbl, term_t t, uint64_t a, bvpoly_buffer_t *b) {
  addmul_bvterm64_to_buffer(tbl, t, -a, b);
}


/*
 * ADD d * t TO A BUFFER: general case
 */

/*
 * Add d * (c + 2^k * x) or d * (c + 2^k * (bvnot x)) to b
 * - numbits > 64
 * - k is given by cscan->numbits
 * - c is stored in cscan->val
 * - c is smaller than 2^k
 *
 * Side effect: cscan->val is modified
 */
static void addmul_decomp_to_buffer(bvpoly_buffer_t *b, bvconst_scan_result_t *cscan, term_t x, bool negated, uint32_t *d) {
  uint32_t k;

  assert(cscan->bitsize == bvpoly_buffer_bitsize(b) && cscan->bitsize > 64);

  k = cscan->numbits;
  assert(k < cscan->bitsize);

  if (k == 0) {
    // no constant and 2^k is 1
    if (negated) {
      // add d * (bvnot x) = -d - d * x
      bvpoly_buffer_sub_constant(b, d);
      bvpoly_buffer_sub_monomial(b, x, d);
    } else {
      // add d * x
      bvpoly_buffer_add_monomial(b, x, d);
    }
  } else {
    // constant c stored in cscan->val:
    // add d * c to buffer b
    bvpoly_buffer_addmul_constant(b, cscan->val, d);

    // now add d * 2^k * x or d * 2^k * (bvnot x)
    // we first compute d * 2^k in cscan->val
    bvconst_set(cscan->val, cscan->width, d);
    bvconst_shift_left(cscan->val, cscan->bitsize, k, 0);

    if (negated) {
      // add d * (2^k * (bvnot x)) = - d * 2^k - d * 2^k * x
      bvpoly_buffer_sub_constant(b, cscan->val);
      bvpoly_buffer_sub_monomial(b, x, cscan->val);
    } else {
      // add 2^ k * x
      bvpoly_buffer_add_monomial(b, x, cscan->val);
    }
  }
}


/*
 * Add a * bit-array term t to buffer b
 * - try to convert t to an arithmetic expression
 */
static void addmul_bvarray_to_buffer(const term_table_t *tbl, term_t t, bvpoly_buffer_t *b, uint32_t *a) {
  composite_term_t *bits;
  bvconst_scan_result_t cscan;
  bvscan_result_t vscan;
  uint32_t n;
  term_t x;

  assert(term_kind(tbl, t) == BV_ARRAY);

  bits = bvarray_term_desc(tbl, t);
  n = bits->arity;
  assert(0 < n && n == bvpoly_buffer_bitsize(b));

  init_bvconst_scan(&cscan, n);
  if (convert_bvarray(tbl, &cscan, &vscan, n, bits->arg)) {
    // success: t is c + 2^k * x or c + 2^k * (bvnot x)
    // k is stored in cscan.numbits
    // c is stored in cscan.val
    x = vscan.term;
    assert(term_bitsize(tbl, x) == n);
    addmul_decomp_to_buffer(b, &cscan, x, vscan.negated, a);

  } else {
    // can't rewrite t to an arithmetic expression
    bvpoly_buffer_add_monomial(b, t, a);
  }

  delete_bvconst_scan(&cscan);
}


/*
 * Add a * t to buffer b
 * - attempt to convert t to an arithmetic expression
 */
void addmul_bvterm_to_buffer(term_table_t *tbl, term_t t, uint32_t *a, bvpoly_buffer_t *b) {
  assert(is_bitvector_term(tbl, t) && term_bitsize(tbl, t) == bvpoly_buffer_bitsize(b));
  assert(term_bitsize(tbl, t) > 64);

  switch (term_kind(tbl, t)) {
  case BV_CONSTANT:
    bvpoly_buffer_addmul_constant(b, bvconst_term_desc(tbl, t)->data, a);
    break;

  case BV_POLY:
    bvpoly_buffer_addmul_poly(b, bvpoly_term_desc(tbl, t), a);
    break;

  case BV_ARRAY:
    addmul_bvarray_to_buffer(tbl, t, b, a);
    break;

  default:
    bvpoly_buffer_add_monomial(b, t, a);
    break;
  }

}


/*
 * Subtract d * t FROM A BUFFER: general case
 */

/*
 * Subtract d * (c + 2^k * x) or d * (c + 2^k * (bvnot x)) from b
 * - numbits > 64
 * - k is given by cscan->numbits
 * - c is stored in cscan->val
 * - c is smaller than 2^k
 *
 * Side effect: cscan->val is modified
 */
static void submul_decomp_from_buffer(bvpoly_buffer_t *b, bvconst_scan_result_t *cscan, term_t x, bool negated, uint32_t *d) {
  uint32_t k;

  assert(cscan->bitsize == bvpoly_buffer_bitsize(b) && cscan->bitsize > 64);

  k = cscan->numbits;
  assert(k < cscan->bitsize);

  if (k == 0) {
    // no constant and 2^k is 1
    if (negated) {
      // subtract d * (bvnot x) = -d - d * x
      bvpoly_buffer_add_constant(b, d);
      bvpoly_buffer_add_monomial(b, x, d);
    } else {
      // subtract d * x
      bvpoly_buffer_sub_monomial(b, x, d);
    }
  } else {
    // constant c stored in cscan->val:
    // subtract d * c from buffer b
    bvpoly_buffer_submul_constant(b, cscan->val, d);

    // now subtract d * 2^k * x or d * 2^k * (bvnot x)
    // we first compute d * 2^k in cscan->val
    bvconst_set(cscan->val, cscan->width, d);
    bvconst_shift_left(cscan->val, cscan->bitsize, k, 0);

    if (negated) {
      // subtract d * (2^k * (bvnot x)) = - d * 2^k - d * 2^k * x
      bvpoly_buffer_add_constant(b, cscan->val);
      bvpoly_buffer_add_monomial(b, x, cscan->val);
    } else {
      // subtract 2^ k * x
      bvpoly_buffer_sub_monomial(b, x, cscan->val);
    }
  }
}

/*
 * Subtract a * bit-array term t from buffer b
 * - try to convert t to an arithmetic expression
 */
static void submul_bvarray_from_buffer(const term_table_t *tbl, term_t t, bvpoly_buffer_t *b, uint32_t *a) {
  composite_term_t *bits;
  bvconst_scan_result_t cscan;
  bvscan_result_t vscan;
  uint32_t n;
  term_t x;

  assert(term_kind(tbl, t) == BV_ARRAY);

  bits = bvarray_term_desc(tbl, t);
  n = bits->arity;
  assert(0 < n && n == bvpoly_buffer_bitsize(b));

  init_bvconst_scan(&cscan, n);
  if (convert_bvarray(tbl, &cscan, &vscan, n, bits->arg)) {
    // success: t is c + 2^k * x or c + 2^k * (bvnot x)
    // k is stored in cscan.numbits
    // c is stored in cscan.val
    x = vscan.term;
    assert(term_bitsize(tbl, x) == n);
    submul_decomp_from_buffer(b, &cscan, x, vscan.negated, a);

  } else {
    // can't rewrite t to an arithmetic expression
    bvpoly_buffer_sub_monomial(b, t, a);
  }

  delete_bvconst_scan(&cscan);
}



/*
 * Subtract a * t from buffer b
 * - attempt to convert t to an arithmetic expression
 */
void submul_bvterm_from_buffer(term_table_t *tbl, term_t t, uint32_t *a, bvpoly_buffer_t *b) {
  assert(is_bitvector_term(tbl, t) && term_bitsize(tbl, t) == bvpoly_buffer_bitsize(b));
  assert(term_bitsize(tbl, t) > 64);

  switch (term_kind(tbl, t)) {
  case BV_CONSTANT:
    bvpoly_buffer_submul_constant(b, bvconst_term_desc(tbl, t)->data, a);
    break;

  case BV_POLY:
    bvpoly_buffer_submul_poly(b, bvpoly_term_desc(tbl, t), a);
    break;

  case BV_ARRAY:
    submul_bvarray_from_buffer(tbl, t, b, a);
    break;

  default:
    bvpoly_buffer_sub_monomial(b, t, a);
    break;
  }

}





/***********************************
 *  FACTORING OF BIT-VECTOR TERMS  *
 **********************************/

static bool bvpoly64_is_bvprod(bvpoly64_t *p) {
  if (p->nterms == 1) {
    assert(p->mono[0].coeff != 0 && p->mono[0].coeff != 1);
    return true;
  }
  return false;
}

static  bool bvpoly_is_bvprod(bvpoly_t *p) {
  if (p->nterms == 1) {
    assert(!bvconst_is_zero(p->mono[0].coeff, p->width) &&
	   !bvconst_is_one(p->mono[0].coeff, p->width));
    return true;
  }
  return false;
}

/*
 * Check whether t is a product
 * - this returns true if t is (bvshl x y) since (bvshl x y) = x * (bvshl 1 y)
 *   or if t is a power-product
 *   of if t is a polynomial with a single monomial = a * power-product for
 *   some constant a that's not 0 and not 1.
 * - return false otherwise (including if t is not a bit-vector term).
 */
bool term_is_bvprod(term_table_t *tbl, term_t t) {
  assert(good_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV_SHL:
  case POWER_PRODUCT:
    return true;

  case BV64_POLY:
    return bvpoly64_is_bvprod(bvpoly64_term_desc(tbl, t));

  case BV_POLY:
    return bvpoly_is_bvprod(bvpoly_term_desc(tbl, t));

  default:
    return false;
  }
}



/*
 * Add d * t to the exponent part of b
 */
static void get_exponents(term_table_t *tbl, bvfactor_buffer_t *b, term_t t, uint32_t d) {
  // for now we don't expand t.
  bvfactor_buffer_exp(b, t, d);
}


/*
 * Recursive factoring:
 * - compute a factorization of t^d and add it to buffer b
 */
static void get_factors(term_table_t *tbl, bvfactor_buffer_t *b, term_t t, uint32_t d);

static void bvfactor_const64(bvfactor_buffer_t *b, bvconst64_term_t *c, uint32_t d) {
  assert(c->bitsize == b->bitsize);
  bvfactor_buffer_mulconst64(b, c->value, d);
}

static void bvfactor_const(bvfactor_buffer_t *b, bvconst_term_t *c, uint32_t d) {
  assert(c->bitsize == b->bitsize);
  bvfactor_buffer_mulconst(b, c->data, d);
}

static void bvfactor_shl(term_table_t *tbl, bvfactor_buffer_t *b, composite_term_t *shl, uint32_t d) {
  // shl is (bvshl x y) = x * 2^y
  get_factors(tbl, b, shl->arg[0], d);
  get_exponents(tbl, b, shl->arg[1], d);
}

static void bvfactor_pprod(term_table_t *tbl, bvfactor_buffer_t *b, term_t t, uint32_t d) {
  pprod_t *p;
  uint32_t i, n;
  uint64_t test_degree;

  p = pprod_term_desc(tbl, t);

  /*
   * We check that the degree won't overflow.
   * If there's a risk, we don't expand t.
   */
  test_degree = (uint64_t) d * p->degree;
  if (test_degree >= 20 || b->total_degree > UINT64_MAX - test_degree) {
    bvfactor_buffer_mul(b, t, d);
    return;
  }

  n = p->len;
  for (i=0; i<n; i++) {
    //     p->prod[i] is x_i ^ d_i
    assert((uint64_t) d * p->prod[i].exp <= UINT32_MAX);
    get_factors(tbl, b, p->prod[i].var, d * p->prod[i].exp);
  }
}

static void bvfactor_poly64(term_table_t *tbl, bvfactor_buffer_t *b, term_t t, uint32_t d) {
  bvpoly64_t *p;

  p = bvpoly64_term_desc(tbl, t);
  if (bvpoly64_is_bvprod(p)) {
    // p is a * x for some constant a and term x
    assert(p->nterms == 1 && is_bitvector_term(tbl, p->mono[0].var));
    bvfactor_buffer_mulconst64(b, p->mono[0].coeff, d);
    get_factors(tbl, b, p->mono[0].var, d);
  } else {
    bvfactor_buffer_mul(b, t, d);
  }
}

static void bvfactor_poly(term_table_t *tbl, bvfactor_buffer_t *b, term_t t, uint32_t d) {
  bvpoly_t *p;

  p = bvpoly_term_desc(tbl, t);
  if (bvpoly_is_bvprod(p)) {
    // p is a * x for some constant a and term x
    assert(p->nterms == 1 && is_bitvector_term(tbl, p->mono[0].var));
    bvfactor_buffer_mulconst(b, p->mono[0].coeff, d);
    get_factors(tbl, b, p->mono[0].var, d);
  } else {
    bvfactor_buffer_mul(b, t, d);
  }
}



/*
 * Decompose t^d into factors and add the factors to buffer b
 * - t is a bitvector term
 * - the buffer is initialized with the right bitsize
 */
static void get_factors(term_table_t *tbl, bvfactor_buffer_t *b, term_t t, uint32_t d) {
  assert(is_bitvector_term(tbl, t) && term_bitsize(tbl, t) == b->bitsize);

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    bvfactor_const64(b, bvconst64_term_desc(tbl, t), d);
    break;

  case BV_CONSTANT:
    bvfactor_const(b, bvconst_term_desc(tbl, t), d);
    break;

  case BV_SHL:
    bvfactor_shl(tbl, b, bvshl_term_desc(tbl, t), d);
    break;

  case POWER_PRODUCT:
    bvfactor_pprod(tbl, b, t, d);
    break;

  case BV64_POLY:
    bvfactor_poly64(tbl, b, t, d);
    break;

  case BV_POLY:
    bvfactor_poly(tbl, b, t, d);
    break;

  default:
    bvfactor_buffer_mul(b, t, d);
    break;
  }
}


/*
 * Construct the factorization of term t
 * - store the result in buffer b
 * - b must be initialized
 */
void factor_bvterm(term_table_t *tbl, term_t t, bvfactor_buffer_t *b) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));
  n = term_bitsize(tbl, t);
  reset_bvfactor_buffer(b, n);
  get_factors(tbl, b, t, 1);
  bvfactor_buffer_normalize(b);
}


/*
 * Add factors of (a * t) to buffer b
 * - t must be a bitvector term
 * - b and t must have the same bitsize
 * - if t has 64bits or less, a is given as a 64bit constant
 * - if t has more than 64bits, a is given as an array of 32bit words
 */
void factor_mul_bvterm64(term_table_t *tbl, uint64_t a, term_t t, bvfactor_buffer_t *b) {
  assert(is_bitvector_term(tbl, t));
  assert(b->bitsize <= 64 && b->bitsize == term_bitsize(tbl, t));

  bvfactor_buffer_mulconst64(b, a, 1);
  get_factors(tbl, b, t, 1);
  bvfactor_buffer_normalize(b);
}

void factor_mul_bvterm(term_table_t *tbl, uint32_t *a, term_t t,  bvfactor_buffer_t *b) {
  assert(is_bitvector_term(tbl, t));
  assert(b->bitsize > 64 && b->bitsize == term_bitsize(tbl, t));

  bvfactor_buffer_mulconst(b, a, 1);
  get_factors(tbl, b, t, 1);
  bvfactor_buffer_normalize(b);
}


/*
 * Compute the factorization of all monomials in p
 * - the factoring of p->mono[i] is stored in b[i]
 */
void factor_bvpoly64_monomials(term_table_t *tbl, bvpoly64_t *p, bvfactor_buffer_t *b) {
  uint32_t i, n;

  assert(0 < p->bitsize && p->bitsize <= 64);

  n = p->nterms;
  for (i=0; i<n; i++) {
    reset_bvfactor_buffer(b+i, p->bitsize);
    bvfactor_buffer_mulconst64(b+i, p->mono[i].coeff, 1);
    if (p->mono[i].var != const_idx) {
      get_factors(tbl, b+i, p->mono[i].var, 1);
    }
    bvfactor_buffer_normalize(b+i);
  }
}

void factor_bvpoly_monomials(term_table_t *tbl, bvpoly_t *p, bvfactor_buffer_t *b) {
  uint32_t i, n;

  assert(64 < p->bitsize);

  n = p->nterms;
  for (i=0; i<n; i++) {
    reset_bvfactor_buffer(b+i, p->bitsize);
    bvfactor_buffer_mulconst(b+i, p->mono[i].coeff, 1);
    if (p->mono[i].var != const_idx) {
      get_factors(tbl, b+i, p->mono[i].var, 1);
    }
    bvfactor_buffer_normalize(b+i);
  }
}



/*************************************
 *  TERMS BUILT FROM FACTOR BUFFERS  *
 ************************************/

/*
 * Check whether product * 2^exponent is equal to 1
 * - i.e., both produce and exponent are empty
 */
static bool bvfactor_buffer_is_unit(bvfactor_buffer_t *b) {
  return bvfactor_buffer_product_is_one(b) && bvfactor_buffer_exponent_is_zero(b);
}

/*
 * Construct term t for the constant part of b
 */
static term_t bvfactor_constant_to_term(term_table_t *tbl, bvfactor_buffer_t *b) {
  uint32_t n;
  term_t t;

  n = b->bitsize;
  assert(n > 0);

  if (n <= 64) {
    assert(norm64(b->constant64, n) == b->constant64);
    t = bv64_constant(tbl, n, b->constant64);
  } else {
    assert(bvconstant_is_normalized(&b->constant) && b->constant.bitsize == n);
    t = bvconst_term(tbl, n, b->constant.data);
  }
  return t;
}

/*
 * Construct term t for the product part of b
 * - must not be used if the produce is empty
 */
static term_t bvfactor_product_to_term(term_table_t *tbl, bvfactor_buffer_t *b) {
  assert(! bvfactor_buffer_product_is_one(b));
  return pprod_term_from_buffer(tbl, &b->product);
}

/*
 * Build a term t from a bvpoly_buffer b
 * - the buffer must be normalized and non-zero
 */
static term_t bvpoly_buffer_to_term(term_table_t *tbl, bvpoly_buffer_t *b) {
  uint32_t nbits;
  term_t t;
  uint64_t c;
  uint32_t *d;

  assert(bvpoly_buffer_num_terms(b) > 0);

  if (bvpoly_buffer_is_constant(b)) {
    // constant given by coeff 0 of b
    nbits = bvpoly_buffer_bitsize(b);
    if (nbits <= 64) {
      c = bvpoly_buffer_coeff64(b, 0);
      assert(norm64(c, nbits) == c);
      t = bv64_constant(tbl, nbits, c);
    } else {
      d = bvpoly_buffer_coeff(b, 0);
      assert(bvconst_is_normalized(d, nbits));
      t = bvconst_term(tbl, nbits, d);
    }
    return t;
  }

  if (bvpoly_buffer_is_var(b, &t)) {
    // polynomial of the form 1 * t
    assert(good_term(tbl, t));
    return t;
  }

  return bv_poly_from_buffer(tbl, b);
}

/*
 * Build the term t = product * 2^exponent = bvshl(product, exponent)
 * when it's known that the product is not empty
 */
static term_t bvfactor_full_prod_to_term(term_table_t *tbl, bvfactor_buffer_t *b) {
  term_t e, t;

  t = bvfactor_product_to_term(tbl, b);
  if (! bvfactor_buffer_exponent_is_zero(b)) {
    e = bvpoly_buffer_to_term(tbl, &b->exponent);
    t = bvshl_term(tbl, t, e); // t << e
  }
  return t;
}

/*
 * Build the term t = bvshl(constant, exponent) (when the product is empty)
 * the exponent must not be zero.
 */
static term_t bvfactor_constant_shift_expo(term_table_t *tbl, bvfactor_buffer_t *b) {
  term_t e, t;

  t = bvfactor_constant_to_term(tbl, b);
  e = bvpoly_buffer_to_term(tbl, &b->exponent);
  return bvshl_term(tbl, t, e);
}

/*
 * Construct a term t from buffer b:
 * - if b contains C * product * 2^exponent
 *   then this constructs two auxiliary terms:
 *    p := product
 *    e := exponent
 *   and returns C * bvshl(p, e)
 * - to build the terms, we need an auxiliary bvpoly_buffer_t aux
 */
term_t bvfactor_buffer_to_term(term_table_t *tbl, bvpoly_buffer_t *aux, bvfactor_buffer_t *b) {
  uint32_t n;
  term_t t;

  if (bvfactor_buffer_is_zero(b) || bvfactor_buffer_is_unit(b)) {
    // result = constant part of b
    return bvfactor_constant_to_term(tbl, b);
  }

  if (bvfactor_buffer_product_is_one(b)) {
    // result = bvshl(constant, exponent)
    return bvfactor_constant_shift_expo(tbl, b);
  }

  // general case: result = constant * bvshl(product, exponent)
  t = bvfactor_full_prod_to_term(tbl, b);
  n = b->bitsize;
  reset_bvpoly_buffer(aux, n);
  if (n <= 64) {
    bvpoly_buffer_add_mono64(aux, t, b->constant64);
  } else {
    bvpoly_buffer_add_monomial(aux, t, b->constant.data);
  }
  normalize_bvpoly_buffer(aux);

  return bvpoly_buffer_to_term(tbl, aux);
}


/*
 * Convert b to a term t than add the term to buffer aux
 * - b must be normalized
 * - aux must have the same bitsize as b
 */
static void bvpoly_buffer_add_factor(term_table_t *tbl, bvpoly_buffer_t *aux, bvfactor_buffer_t *b) {
  term_t t;

  if (bvfactor_buffer_is_zero(b)) return;

  if (bvfactor_buffer_is_unit(b)) {
    // add constant
    if (b->bitsize <= 64) {
      bvpoly_buffer_add_const64(aux, b->constant64);
    } else {
      bvpoly_buffer_add_constant(aux, b->constant.data);
    }

  } else if (bvfactor_buffer_product_is_one(b)) {
    // add bvshl(constant, exponent)
    t = bvfactor_constant_shift_expo(tbl, b);
    bvpoly_buffer_add_var(aux, t);

  } else {
    // add constant * bvshl(product, exponent)
    t = bvfactor_full_prod_to_term(tbl, b);
    if (b->bitsize <= 64) {
      bvpoly_buffer_add_mono64(aux, t, b->constant64);
    } else {
      bvpoly_buffer_add_monomial(aux, t, b->constant.data);
    }
  }
}

/*
 * Construct a term t = bvzero with n bits
 */
static term_t zero_bv_constant(term_table_t *tbl, uint32_t nbits) {
  uint32_t aux[8]; // to save a call to malloc is nbits <= 256
  uint32_t *a;
  uint32_t w;
  term_t t;

  if (nbits <= 64) {
    t = bv64_constant(tbl, nbits, 0);
  } else {
    w = (nbits + 31) >> 5;
    if (w <= 8) {
      bvconst_clear(aux, w);
      t = bvconst_term(tbl, nbits, aux);
    } else {
      a = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
      bvconst_clear(a, w);
      t = bvconst_term(tbl, nbits, a);
      safe_free(a);
    }
  }

  return t;
}

/*
 * Construct a term t from an array of n buffers b[0 ... n-1]
 * - n must be positive
 * - this constructs a sum of n terms t_0 .... t_n-1
 *   where t_i is the conversion of b[i] to a term.
 */
term_t bvfactor_buffer_array_to_term(term_table_t *tbl, bvpoly_buffer_t *aux, bvfactor_buffer_t *b, uint32_t n) {
  uint32_t i, nbits;

  assert(n > 0);

  nbits = b[0].bitsize;
  reset_bvpoly_buffer(aux, nbits);
  for (i=0; i<n; i++) {
    bvpoly_buffer_add_factor(tbl, aux, b+i);
  }
  normalize_bvpoly_buffer(aux);

  if (bvpoly_buffer_is_zero(aux)) {
    return zero_bv_constant(tbl, nbits);
  } else {
    return bvpoly_buffer_to_term(tbl, aux);
  }
}



/*****************************************
 *  SIMPLIFICATION OF BIT-VECTOR TERMS   *
 ****************************************/

/*
 * Get bit i of term t:
 * - return NULL_TERM if the bit can't be determined
 * - return true or false if t is a bitvector constant
 * - return b_i if t is (bv-array b_0 .. b_i ...)
 *
 * t must be a bitvector term of size > i
 */
term_t extract_bit(term_table_t *tbl, term_t t, uint32_t i) {
  uint32_t *d;
  uint64_t c;
  term_t bit;

  assert(is_bitvector_term(tbl, t) && term_bitsize(tbl, t) > i);

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    c = bvconst64_term_desc(tbl, t)->value;
    bit = bool2term(tst_bit64(c, i));
    break;

  case BV_CONSTANT:
    d = bvconst_term_desc(tbl, t)->data;
    bit = bool2term(bvconst_tst_bit(d, i));
    break;

  case BV_ARRAY:
    bit = bvarray_term_desc(tbl, t)->arg[i];
    break;

  default:
    bit = NULL_TERM;
    break;
  }

  return bit;
}




/*
 * Check whether (eq b c) simplifies and if so returns the result.
 * - b and c must be boolean terms (assumed not opposite of each other).
 * - return NULL_TERM if no simplification is found
 *
 * Rules:
 *   (eq b b)     --> true
 *   (eq b true)  --> b
 *   (eq b false) --> (not b)
 * + symmetric cases for the last two rules
 */
static term_t check_biteq_simplifies(term_t b, term_t c) {
  assert(! opposite_bool_terms(b, c));

  if (b == c) return true_term;

  if (b == true_term)  return c;
  if (b == false_term) return opposite_term(c); // not c
  if (c == true_term)  return b;
  if (c == false_term) return opposite_term(b);

  return NULL_TERM;
}


/*
 * Check whether (and a (eq b c)) simplifies and, if so, returns the result.
 * - a, b, and c are three boolean terms.
 * - return NULL_TERM if no cheap simplification is found
 *
 * We assume that the cheaper simplification tests have been tried before:
 * (i.e., we assume a != false and  b != (not c)).
 */
static term_t check_accu_biteq_simplifies(term_t a, term_t b, term_t c) {
  term_t eq;


  // first check whether (eq b c) simplifies
  eq = check_biteq_simplifies(b, c);
  if (eq == NULL_TERM) return NULL_TERM;

  /*
   * try to simplify (and a eq)
   */
  assert(a != false_term && eq != false_term);

  if (a == eq) return a;
  if (opposite_bool_terms(a, eq)) return false_term;

  if (a == true_term) return eq;
  if (eq == true_term) return a;

  return NULL_TERM;
}



/*
 * Check whether (bveq u v) simplifies:
 * - u is a bitvector constant of no more than 64 bits
 * - v is a bv_array term
 *
 * Return NULL_TERM if no cheap simplification is found.
 */
static term_t check_eq_bvconst64(bvconst64_term_t *u, composite_term_t *v) {
  uint32_t i, n;
  term_t accu, b;

  n = u->bitsize;
  assert(n == v->arity);
  accu = true_term;

  for (i=0; i<n; i++) {
    b = bool2term(tst_bit64(u->value, i)); // bit i of u
    accu = check_accu_biteq_simplifies(accu, b, v->arg[i]);
    if (accu == NULL_TERM || accu == false_term) {
      break;
    }
  }

  return accu;
}


/*
 * Same thing for a generic constant u.
 */
static term_t check_eq_bvconst(bvconst_term_t *u, composite_term_t *v) {
  uint32_t i, n;
  term_t accu, b;

  n = u->bitsize;
  assert(n == v->arity);
  accu = true_term;

  for (i=0; i<n; i++) {
    b = bool2term(bvconst_tst_bit(u->data, i)); // bit i of u
    accu = check_accu_biteq_simplifies(accu, b, v->arg[i]);
    if (accu == NULL_TERM || accu == false_term) {
      break;
    }
  }

  return accu;
}


/*
 * Same thing for two bv_array terms
 */
static term_t check_eq_bvarray(composite_term_t *u, composite_term_t *v) {
  uint32_t i, n;
  term_t accu;

  n = u->arity;
  assert(n == v->arity);
  accu = true_term;

  for (i=0; i<n; i++) {
    accu = check_accu_biteq_simplifies(accu, u->arg[i], v->arg[i]);
    if (accu == NULL_TERM || accu == false_term) {
      break;
    }
  }

  return accu;
}



/*
 * Try to simplify (bv-eq t1 t2) to a boolean term
 * - if t1 and t2 can be rewritten as arrays of bits
 *   [b0 .. b_n] and [c_0 ... c_n], respectively,
 *   then the function checks whether
 *      (and (b0 == c0) ... (b_n == c_n))
 *   simplifies to a single boolean term.
 * - return NULL_TERM if no simplification is found
 */
term_t simplify_bveq(term_table_t *tbl, term_t t1, term_t t2) {
  term_kind_t k1, k2;
  term_t aux;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2) &&
         term_bitsize(tbl, t1) == term_bitsize(tbl, t2));

  k1 = term_kind(tbl, t1);
  k2 = term_kind(tbl, t2);
  aux = NULL_TERM;
  switch (k1) {
  case BV64_CONSTANT:
    if (k2 == BV_ARRAY) {
      aux = check_eq_bvconst64(bvconst64_term_desc(tbl, t1), bvarray_term_desc(tbl, t2));
    }
    break;

  case BV_CONSTANT:
    if (k2 == BV_ARRAY) {
      aux = check_eq_bvconst(bvconst_term_desc(tbl, t1), bvarray_term_desc(tbl, t2));
    }
    break;

  case BV_ARRAY:
    if (k2 == BV64_CONSTANT) {
      aux = check_eq_bvconst64(bvconst64_term_desc(tbl, t2), bvarray_term_desc(tbl, t1));
    } else if (k2 == BV_CONSTANT) {
      aux = check_eq_bvconst(bvconst_term_desc(tbl, t2), bvarray_term_desc(tbl, t1));
    } else if (k2 == BV_ARRAY) {
      aux = check_eq_bvarray(bvarray_term_desc(tbl, t1), bvarray_term_desc(tbl, t2));
    }
    break;

  default:
    break;
  }


  return aux;
}


/*
 * Convert (bveq u v) to a conjunction of boolean terms
 * - u is a BV64 constant, v is a bitarray
 * - store the result in vector a
 */
static void flatten_eq_bvconst64(bvconst64_term_t *u, composite_term_t *v, ivector_t *a) {
  uint32_t i, n;
  term_t aux, b;

  n = u->bitsize;
  assert(n == v->arity);
  for (i=0; i<n; i++) {
    b = bool2term(tst_bit64(u->value, i)); // bit i of u
    aux = check_biteq_simplifies(b, v->arg[i]);
    assert(aux != NULL_TERM);

    if (aux != true_term) {
      ivector_push(a, aux);
    }
  }
}


/*
 * Same thing when u is a BV constant and v is a bitarray
 */
static void flatten_eq_bvconst(bvconst_term_t *u, composite_term_t *v, ivector_t *a) {
  uint32_t i, n;
  term_t aux, b;

  n = u->bitsize;
  assert(n == v->arity);
  for (i=0; i<n; i++) {
    b = bool2term(bvconst_tst_bit(u->data, i)); // bit i of u
    aux = check_biteq_simplifies(b, v->arg[i]);
    assert(aux != NULL_TERM);

    if (aux != true_term) {
      ivector_push(a, aux);
    }
  }
}


/*
 * Try to convert (bveq u v) to a conjunction of Boolean terms
 * - u and v are bit arrays of the same size
 * - return true if that succeeds
 */
static bool flatten_eq_bvarray(composite_term_t *u, composite_term_t *v, ivector_t *a) {
  uint32_t i, n;
  term_t aux;

  n = u->arity;
  assert(n == v->arity);
  for (i=0; i<n; i++) {
    aux = check_biteq_simplifies(u->arg[i], v->arg[i]);
    if (aux == NULL_TERM) return false; // failed
    if (aux != true_term) {
      ivector_push(a, aux);
    }
  }

  return true;
}


/*
 * Try to simplify (bv-eq t1 t2) to a conjunction of terms
 * - if t1 and t2 can be rewritten as arrays of bits
 *   [b_0 ... b_n] and [c_0 ... c_n], respectively,
 *   then the function checks whether each
 *   equality (b_i == c_i)  simplifies to a single Boolean term e_i
 * - if all of them do, then the function
 *   returns true and adds e_0, ... e_n to vector v
 *
 * As above: t1 and t2 must not be equal, and disequal_bitvector_terms(tbl, t1, t2)
 * must be false.
 */
bool bveq_flattens(term_table_t *tbl, term_t t1, term_t t2, ivector_t *v) {
  term_kind_t k1, k2;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2) &&
         term_bitsize(tbl, t1) == term_bitsize(tbl, t2));

  k1 = term_kind(tbl, t1);
  k2 = term_kind(tbl, t2);
  switch (k1) {
  case BV64_CONSTANT:
    if (k2 == BV_ARRAY) {
      flatten_eq_bvconst64(bvconst64_term_desc(tbl, t1), bvarray_term_desc(tbl, t2), v);
      return true;
    }
    break;

  case BV_CONSTANT:
    if (k2 == BV_ARRAY) {
      flatten_eq_bvconst(bvconst_term_desc(tbl, t1), bvarray_term_desc(tbl, t2), v);
      return true;
    }
    break;

  case BV_ARRAY:
    if (k2 == BV64_CONSTANT) {
      flatten_eq_bvconst64(bvconst64_term_desc(tbl, t2), bvarray_term_desc(tbl, t1), v);
      return true;
    } else if (k2 == BV_CONSTANT) {
      flatten_eq_bvconst(bvconst_term_desc(tbl, t2), bvarray_term_desc(tbl, t1), v);
      return true;
    } else if (k2 == BV_ARRAY) {
      return flatten_eq_bvarray(bvarray_term_desc(tbl, t1), bvarray_term_desc(tbl, t2), v);
    }
    break;

  default:
    break;
  }

  return false;
}


/*****************************************
 *  INTERVAL ABSTRACTION FOR BITVECTORS  *
 ****************************************/

/*
 * Compute the abstraction of t^d then multiply a by that
 * - the result is stored in a
 * - returned value: true means that a has some information
 *   (i.e., more precise than the full abstraction for n bits)
 * - if the returned value is false, then the default abstraction
 *   is copied in a
 */
static bool bv64_mulpower_abs(term_table_t *tbl, term_t t, uint32_t d, uint32_t n, bv64_abs_t *a) {
  bv64_abs_t aux;
  bool nontrivial;

  assert(is_bitvector_term(tbl, t) && n == term_bitsize(tbl, t));
  assert(1 <= n && n <= 64 && d >= 1);

  bv64_abstract_term(tbl, t, &aux);
  nontrivial = bv64_abs_nontrivial(&aux, n);
  if (d>1 && nontrivial) {
    bv64_abs_power(&aux, d);
    nontrivial = bv64_abs_nontrivial(&aux, n);
  }
  if (nontrivial) {
    bv64_abs_mul(a, &aux);
    nontrivial = bv64_abs_nontrivial(a, n);
  }
  if (!nontrivial) {
    bv64_abs_default(a, n);
  }

  return nontrivial;
}


/*
 * Compute the abstraction of c * t then add that to a
 * - store the result in a
 * - return true is the result has some information (more
 *   precise than the full abstraction for n bits)
 * - return false otherwise and set a to the default
 *   abstraction for n bits
 */
static bool bv64_addmul_abs(term_table_t *tbl, term_t t, uint64_t c, uint32_t n, bv64_abs_t *a) {
  bv64_abs_t aux;
  bool nontrivial;

  assert(is_bitvector_term(tbl, t) && n == term_bitsize(tbl, t));
  assert(1 <= n && n <= 64 && c == norm64(c, n));

  bv64_abstract_term(tbl, t, &aux);
  nontrivial = bv64_abs_nontrivial(&aux, n);
  if (c != 1 && nontrivial) {
    bv64_abs_mul_const(&aux, c, n);
    nontrivial = bv64_abs_nontrivial(&aux, n);
  }
  if (nontrivial) {
    bv64_abs_add(a, &aux);
    nontrivial = bv64_abs_nontrivial(a, n);
  }
  if (!nontrivial) {
    bv64_abs_default(a, n);
  }

  return nontrivial;
}


/*
 * Abstraction for a power product
 * - stops as soon as the abstraction is too imprecise
 * - nbits = number of bits
 *
 * NOTE: we assume that no term in the power product is zero.
 */
void bv64_abs_pprod(term_table_t *tbl, pprod_t *p, uint32_t nbits, bv64_abs_t *a) {
  uint32_t i, n;

  bv64_abs_one(a);

  n = p->len;
  for (i=0; i<n; i++) {
    if (!bv64_mulpower_abs(tbl, p->prod[i].var, p->prod[i].exp, nbits, a)) {
      break;
    }
  }
}


/*
 * Compute the abstraction of c * r then add it to a
 * - nbits = number of bits in c and r
 * - return true if the result is not trivial
 * - return false otherwise and set a to the default abstraction
 */
static bool bv64_addmul_pprod_abs(term_table_t *tbl, pprod_t *r, uint64_t c, uint32_t nbits, bv64_abs_t *a) {
  bv64_abs_t aux;
  bool nontrivial;

  assert(r != empty_pp);

  if (pp_is_var(r)) {
    bv64_abstract_term(tbl, var_of_pp(r), &aux);
  } else {
    bv64_abs_pprod(tbl, r, nbits, &aux);
  }
  nontrivial = bv64_abs_nontrivial(&aux, nbits);
  if (c != 1 && nontrivial) {
    bv64_abs_mul_const(&aux, c, nbits);
    nontrivial = bv64_abs_nontrivial(&aux, nbits);
  }
  if (nontrivial) {
    bv64_abs_add(a, &aux);
    nontrivial = bv64_abs_nontrivial(a, nbits);
  }
  if (!nontrivial) {
    bv64_abs_default(a, nbits);
  }

  return nontrivial;
}


/*
 * Abstraction for a polynomial
 * - stops as soon as the abstraction is too imprecise
 * - nbits = number of bits
 */
void bv64_abs_poly(term_table_t *tbl, bvpoly64_t *p, uint32_t nbits, bv64_abs_t *a) {
  uint32_t i, n;

  assert(p->bitsize == nbits);

  n = p->nterms;
  i = 0;
  if (p->mono[i].var == const_idx) {
    bv64_abs_constant(a, p->mono[i].coeff, nbits);
    i ++;
  } else {
    bv64_abs_zero(a);
  }

  while (i < n) {
    if (!bv64_addmul_abs(tbl, p->mono[i].var, p->mono[i].coeff, nbits, a)) {
      break;
    }
    i ++;
  }
}

/*
 * Abstraction for an bvarith buffer
 * - stops as soon as the abstraction is too imprecise
 * - nbits = number of bits
 */
void bv64_abs_buffer(term_table_t *tbl, bvarith64_buffer_t *b, uint32_t nbits, bv64_abs_t *a) {
  uint32_t i, n;
  bvmlist64_t *q;

  assert(b->bitsize == nbits);

  n = b->nterms;
  q = b->list;
  i = 0;

  // the constant is first
  if (q->prod == empty_pp) {
    bv64_abs_constant(a, q->coeff, nbits);
    i ++;
    q = q->next;
  } else {
    bv64_abs_zero(a);
  }

  while (i<n) {
    if (!bv64_addmul_pprod_abs(tbl, q->prod, q->coeff, nbits, a)) {
      break;
    }
    i ++;
    q = q->next;
  }
}


/*
 * Interval abstraction of a bitvector term t
 * - t must be of type (bitvector n) with n <= 64
 * - the result is stored in *a
 */
void bv64_abstract_term(term_table_t *tbl, term_t t, bv64_abs_t *a) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  n = term_bitsize(tbl, t);
  assert(1 <= n && n <= 64);

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    assert(bvconst64_term_desc(tbl, t)->bitsize == n);
    bv64_abs_constant(a, bvconst64_term_desc(tbl, t)->value, n);
    break;

  case BV_ARRAY:
    assert(bvarray_term_desc(tbl, t)->arity == n);
    bv64_abs_array(a, false_term, bvarray_term_desc(tbl, t)->arg, n);
    break;

  case POWER_PRODUCT:
    bv64_abs_pprod(tbl, pprod_term_desc(tbl, t), n, a);
    break;

  case BV64_POLY:
    bv64_abs_poly(tbl, bvpoly64_term_desc(tbl, t), n, a);
    break;

  default:
    bv64_abs_default(a, n);
    break;
  }
}




/*********************************************
 *  NORMALIZATION OF ARITHMETIC CONSTRAINTS  *
 ********************************************/

/*
 * There are three types of arithmetic atoms in Yices:
 *   ARITH_EQ: [t == 0]
 *   ARITH_GE: [t >= 0]
 *   ARITH_BINEQ: [t1 == t2]
 *
 * We normalize them to check whether two arithmetic literals are
 * incompatible (can't both be true).
 *
 * This is limited to constraints on the same term. For example,
 *   [t == 0] and [not [2 + t >= 0]]
 * are normalized to constraints on t:
 *    t == 0 and  t < -2,
 * which are incompatible.
 */

/*
 * Descriptor of an arithmetic constraint:
 * - all constraints are written in the form <sign> <poly> <op> <constant>
 * - <sign> is either + or -
 * - <op> can be EQ/LE/LT/GE/GT
 * - <poly> is a sum of monomials without constant term
 * - to get a normal form, we set <sign> to - if the first monomial of <poly>
 *   is negative and to + if the first monomial of <poly> is positive.
 *
 * To store the representation:
 * - len = number of monomials in p
 * - poly = pointer to the monomial array
 * - aux[3] = array to build the monomial array if required
 */
typedef enum {
  EQ, LE, LT, GE, GT,
} cmp_op_t;

#define NUM_ARITH_CMP_OP ((uint32_t)(GT+1))

typedef struct arith_constraint_s {
  cmp_op_t op;       // comparison operator
  bool is_pos;       // true if positive sign
  uint32_t len;      // number of monomials in poly
  monomial_t *poly;
  rational_t constant;
  monomial_t aux[3];
} arith_constraint_t;


/*
 * Initialize all rationals coefficients (except aux[2])
 */
static void init_arith_cnstr(arith_constraint_t *cnstr) {
  q_init(&cnstr->constant);
  q_init(&cnstr->aux[0].coeff);
  q_init(&cnstr->aux[1].coeff);
}

/*
 * Clear the constraint descriptor
 */
static void delete_arith_cnstr(arith_constraint_t *cnstr) {
  q_clear(&cnstr->constant);
  q_clear(&cnstr->aux[0].coeff);
  q_clear(&cnstr->aux[1].coeff);
}

/*
 * Store p into cnstr:
 * - p is a0 + a1 t1 + ... + a_n t_n
 * - if a_1 is positive, then we set
 *     cnstr->is_pos = true
 *     cnstr->poly = a1 t1 + ... + a_n t_n
 *     cnstr->constant = - a0
 * - if a_1 is negative, then we store
 *     cnstr->is_pos = false
 *     cnstr->poly = a1 t1 + ... + a_n t_n
 *     cnstr->constant = +a0
 *
 * When this function is called, we know that p occurs in an
 * atom of the form (p == 0) or (p >= 0). Then we can assume
 * that p is not a constant polynomial (otherwise the atom would
 * be reduced to true or false  by the term manager).
 */
static void arith_cnstr_set_poly(arith_constraint_t *cnstr, polynomial_t *p) {
  uint32_t n;

  n = p->nterms;
  assert(n >= 1);
  cnstr->is_pos = true;

  if (p->mono[0].var == const_idx) {
    cnstr->len = n - 1;
    cnstr->poly = p->mono + 1;
    q_set_neg(&cnstr->constant, &p->mono[0].coeff);
  } else {
    // no constant term in p
    cnstr->len = n;
    cnstr->poly = p->mono;
    q_clear(&cnstr->constant);
  }

  if (q_is_neg(&cnstr->poly[0].coeff)) {
    cnstr->is_pos = false;
    q_neg(&cnstr->constant);
  }
}


/*
 * Store 1 * t into cnstr->aux
 */
static void arith_cnstr_aux_set_term(arith_constraint_t *cnstr, term_t t) {
  q_set_one(&cnstr->aux[0].coeff);
  cnstr->aux[0].var = t;
  cnstr->aux[1].var = max_idx; // end marker
}

/*
 * Store t into cnstr: t should not be a polynomial
 */
static void arith_cnstr_set_term(arith_constraint_t *cnstr, term_t t) {
  arith_cnstr_aux_set_term(cnstr, t);
  cnstr->is_pos = true;
  cnstr->len = 1;
  cnstr->poly = cnstr->aux;
  q_clear(&cnstr->constant);  // constant = 0
}


/*
 * Store t1 - t2 into cnstr:
 * - one of them may be a rational constant
 */
static void arith_cnstr_set_diff(term_table_t *tbl, arith_constraint_t *cnstr, term_t t1, term_t t2) {
  assert(t1 != t2);

  if (term_kind(tbl, t1) == ARITH_CONSTANT) {
    arith_cnstr_aux_set_term(cnstr, t2);
    cnstr->is_pos = true;
    cnstr->len = 1;
    cnstr->poly = cnstr->aux;
    q_set(&cnstr->constant, rational_term_desc(tbl, t1));

  } else if (term_kind(tbl, t2) == ARITH_CONSTANT) {
    arith_cnstr_aux_set_term(cnstr, t1);
    cnstr->is_pos = true;
    cnstr->len = 1;
    cnstr->poly = cnstr->aux;
    q_set(&cnstr->constant, rational_term_desc(tbl, t2));

  } else {
    // store t1 - t2 into aux
    if (t1 < t2) {
      cnstr->is_pos = true;
      q_set_one(&cnstr->aux[0].coeff);
      cnstr->aux[0].var = t1;
      q_set_minus_one(&cnstr->aux[1].coeff);
      cnstr->aux[1].var = t2;
    } else {
      cnstr->is_pos = false;
      q_set_minus_one(&cnstr->aux[0].coeff);
      cnstr->aux[0].var = t2;
      q_set_one(&cnstr->aux[1].coeff);
      cnstr->aux[1].var = t1;
    }
    cnstr->aux[2].var = max_idx; // end marker

    cnstr->len = 2;
    cnstr->poly = cnstr->aux;
    q_clear(&cnstr->constant); // constant = 0
  }
}


/*
 * Store atom t == 0 into descriptor cnstr
 * - t must be an arithmetic term defined in tbl
 */
static void store_arith_eq(term_table_t *tbl, arith_constraint_t *cnstr, term_t t) {
  assert(is_arithmetic_term(tbl, t));

  cnstr->op = EQ;
  if (term_kind(tbl, t) == ARITH_POLY) {
    arith_cnstr_set_poly(cnstr, poly_term_desc(tbl, t));
  } else {
    arith_cnstr_set_term(cnstr, t);
  }
}

/*
 * Store atom t >= 0 into cnstr
 * - t must be an arithmetic term defined in tbl
 */
static void store_arith_geq(term_table_t *tbl, arith_constraint_t *cnstr, term_t t) {
  assert(is_arithmetic_term(tbl, t));

  if (term_kind(tbl, t) == ARITH_POLY) {
    arith_cnstr_set_poly(cnstr, poly_term_desc(tbl, t));
    // op = GE is sign in '+' or LE is sign is '-'
    cnstr->op = cnstr->is_pos ? GE : LE;
  } else {
    arith_cnstr_set_term(cnstr, t);
    assert(cnstr->is_pos);
    cnstr->op = GE;
  }
}

/*
 * Store atom t < 0 into cnstr
 * - t must be an arithmetic term defined in tbl
 */
static void store_arith_lt(term_table_t *tbl, arith_constraint_t *cnstr, term_t t) {
  assert(is_arithmetic_term(tbl, t));

  if (term_kind(tbl, t) == ARITH_POLY) {
    arith_cnstr_set_poly(cnstr, poly_term_desc(tbl, t));
    // op = LT is sign in '+' or GT is sign is '-'
    cnstr->op = cnstr->is_pos ? LT : GT;
  } else {
    arith_cnstr_set_term(cnstr, t);
    assert(cnstr->is_pos);
    cnstr->op = LT;
  }
}

/*
 * Store t1 == t2 into cnstr
 * - we assume t1 and t2 are not polynomials
 */
static void store_arith_bineq(term_table_t *tbl, arith_constraint_t *cnstr, term_t t1, term_t t2) {
  assert(is_arithmetic_term(tbl, t1) && is_arithmetic_term(tbl, t2));
  arith_cnstr_set_diff(tbl, cnstr, t1, t2);
  cnstr->op = EQ;
}


/*
 * Attempt to store the arithmetic literal t into cnstr
 * - return false if this fails: either because t is not an arithmetic literal
 *   or it's of the form (not (t == 0)) or (not (t1 == t2))
 */
static bool arith_cnstr_store_literal(term_table_t *tbl, arith_constraint_t *cnstr, term_t l) {
  composite_term_t *eq;
  term_t t;

  switch (term_kind(tbl, l)) {
  case ARITH_EQ_ATOM:
    if (is_pos_term(l)) {
      t = arith_eq_arg(tbl, l);
      store_arith_eq(tbl, cnstr, t);
      return true;
    }
    break;

  case ARITH_GE_ATOM:
    t = arith_ge_arg(tbl, l);
    if (is_pos_term(l)) {
      store_arith_geq(tbl, cnstr, t);
    } else {
      store_arith_lt(tbl, cnstr, t);
    }
    return true;

  case ARITH_BINEQ_ATOM:
    if (is_pos_term(l)) {
      eq = arith_bineq_atom_desc(tbl, l);
      assert(eq->arity == 2);
      store_arith_bineq(tbl, cnstr, eq->arg[0], eq->arg[1]);
      return true;
    }
    break;

  default:
    break;
  }

  return false;
}


/*
 * Check whether two cnstr1 and cnstr2 are on the same term/polynomial
 */
static bool arith_cnstr_same_poly(arith_constraint_t *cnstr1, arith_constraint_t *cnstr2) {
  if (cnstr1->len == cnstr2->len) {
    if (cnstr1->is_pos == cnstr2->is_pos) {
      return equal_monarrays(cnstr1->poly, cnstr2->poly);
    } else {
      return opposite_monarrays(cnstr1->poly, cnstr2->poly);
    }
  }
  return false;
}


/*
 * Table to check whether two constraints on t are incompatible
 * - each row corresponds to a constraint [t op a] for different ops
 * - each column corresponds to a constraint [t op b] for different ops
 * - the content of the table is a check on constants a and b:
 *   such that ([t op a] /\ [t op b]) is false whenever the check holds
 * - example [t >= a] /\ [t = b] is false if b < a
 */
typedef enum {
  A_NE_B,
  B_LE_A,
  B_LT_A,
  A_LE_B,
  A_LT_B,
  NEVER,
} constant_check_t;

static const uint8_t cnstr_check_table[NUM_ARITH_CMP_OP][NUM_ARITH_CMP_OP] = {
  /* [t = b]  [t <= b]  [t < b]  [t >= b]  [t > b] */
  {  A_NE_B,   B_LT_A,  B_LE_A,   A_LT_B,  A_LE_B }, /* [t = a]  */
  {  A_LT_B,   NEVER,   NEVER,    A_LT_B,  A_LE_B }, /* [t <= a] */
  {  A_LE_B,   NEVER,   NEVER,    A_LE_B,  A_LE_B }, /* [t < a]  */
  {  B_LT_A,   B_LT_A,  B_LE_A,   NEVER,   NEVER },  /* [t >= a] */
  {  B_LE_A,   B_LE_A,  B_LE_A,   NEVER,   NEVER },  /* [t > a]  */
};


/*
 * Check whether cnstr1 and cnstr2 are incompatible
 */
static bool arith_cnstr_disjoint(arith_constraint_t *cnstr1, arith_constraint_t *cnstr2) {
  rational_t *a, *b;

  if (arith_cnstr_same_poly(cnstr1, cnstr2)) {
    a = &cnstr1->constant;
    b = &cnstr2->constant;
    switch (cnstr_check_table[cnstr1->op][cnstr2->op]) {
    case A_NE_B: return q_neq(a, b);
    case B_LE_A: return q_le(b, a);
    case B_LT_A: return q_lt(b, a);
    case A_LE_B: return q_le(a, b);
    case A_LT_B: return q_lt(a, b);

    default: // return false
      break;
    }
  }

  return false;
}



/******************
 *  SUBSUMPTION   *
 *****************/

/*
 * Check whether two arithmetic literals t1 and t2 are incompatible
 */
bool incompatible_arithmetic_literals(term_table_t *tbl, term_t t1, term_t t2) {
  arith_constraint_t cnstr1, cnstr2;
  bool result;

  if (opposite_bool_terms(t1, t2)) {
    result = true;
  } else {
    init_arith_cnstr(&cnstr1);
    init_arith_cnstr(&cnstr2);

    result = false;
    if (arith_cnstr_store_literal(tbl, &cnstr1, t1) &&
	arith_cnstr_store_literal(tbl, &cnstr2, t2)) {
      result = arith_cnstr_disjoint(&cnstr1, &cnstr2);
    }

    delete_arith_cnstr(&cnstr1);
    delete_arith_cnstr(&cnstr2);
  }

  return result;
}


/*
 * Check whether two bitvector literals t1 and t2 are incompatible
 * MORE TO BE DONE
 */
bool incompatible_bitvector_literals(term_table_t *tbl, term_t t1, term_t t2) {
  composite_term_t *eq1, *eq2;
  bool result;
  uint32_t i, j;

  if (opposite_bool_terms(t1, t2)) {
    result = true;
  } else {
    result = false;

    if (is_pos_term(t1) && is_pos_term(t2) &&
	term_kind(tbl, t1) == BV_EQ_ATOM && term_kind(tbl, t2) == BV_EQ_ATOM) {
      eq1 = bveq_atom_desc(tbl, t1);
      eq2 = bveq_atom_desc(tbl, t2);
      assert(eq1->arity == 2 && eq2->arity == 2);

      for (i=0; i<2; i++) {
	for (j=0; j<2; j++) {
	  if (eq1->arg[i] == eq2->arg[j]) {
	    result = disequal_bv_terms(tbl, eq1->arg[1 - i], eq2->arg[1 - j]);
	    goto done;
	  }
	}
      }
    }
  }

 done:
  return result;
}


/*
 * Check whether two Boolean terms t1 and t2
 * are incompatible (i.e., (t1 and t2) is false.
 * - this does very simple checks for now
 */
bool incompatible_boolean_terms(term_table_t *tbl, term_t t1, term_t t2) {
  composite_term_t *eq1, *eq2;
  uint32_t i, j;

  if (is_arithmetic_literal(tbl, t1) && is_arithmetic_literal(tbl, t2)) {
    return incompatible_arithmetic_literals(tbl, t1, t2);
  }
  if (is_bitvector_literal(tbl, t1) && is_bitvector_literal(tbl, t2)) {
    return incompatible_bitvector_literals(tbl, t1, t2);
  }

  if (t1 == false_term || t2 == false_term || opposite_bool_terms(t1, t2)) {
    return true;
  }

  if (is_pos_term(t1) && is_pos_term(t2) &&
      term_kind(tbl, t1) == EQ_TERM && term_kind(tbl, t2) == EQ_TERM) {
    eq1 = eq_term_desc(tbl, t1);
    eq2 = eq_term_desc(tbl, t2);

    for (i=0; i<2; i++) {
      for (j=0; j<2; j++) {
	if (eq1->arg[i] == eq2->arg[j]) {
	  return disequal_bv_terms(tbl, eq1->arg[1 - i], eq2->arg[1 - j]);
	}
      }
    }
  }

  return false;
}


/*
 * Check whether t1 subsumes t2 (i.e., t1 => t2)
 */
bool term_subsumes_term(term_table_t *tbl, term_t t1, term_t t2) {
  return incompatible_boolean_terms(tbl, t1, opposite_term(t2));
}

/*
 * Check whether t1 subsumes all elements of a[0 ... n-1]
 */
bool term_subsumes_array(term_table_t *tbl, term_t t1, uint32_t n, term_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (!term_subsumes_term(tbl, t1, a[i])) {
      return false;
    }
  }

  return true;
}





/****************************
 *  EQUALITY DECOMPOSITION  *
 ***************************/

/*
 * Check whether t is equivalent to (x == a) where x is a term and a is a constant
 * - if so stores the term and constant in *x and *a, and returns true.
 * - otherwise returns false, and leave *x and *a unchanged.
 */
bool is_term_eq_const(term_table_t *tbl, term_t t, term_t *x, term_t *a) {
  composite_term_t *eq;

  assert(good_term(tbl, t));
  if (is_pos_term(t)) {
    switch (term_kind(tbl, t)) {
    case ARITH_EQ_ATOM:
      // t is (x == 0);
      *x = arith_eq_arg(tbl, t);
      *a = zero_term;
      return true;

    case EQ_TERM:
    case ARITH_BINEQ_ATOM:
    case BV_EQ_ATOM:
      eq = composite_term_desc(tbl, t);
      assert(eq->arity == 2);
      if (is_const_term(tbl, eq->arg[0])) {
	*a = eq->arg[0];
	*x = eq->arg[1];
	return true;
      }
      if (is_const_term(tbl, eq->arg[1])) {
	*x = eq->arg[0];
	*a = eq->arg[1];
	return true;
      }
      break;

    default:
      break;
    }

  }

  return false;
}



/*
 * Variant: check whether t is of the form (x == a) where x is uninterpreted and
 * a is a constant.
 */
bool is_unint_eq_const(term_table_t *tbl, term_t t, term_t *x, term_t *a) {
  term_t x0, a0;

  if (is_term_eq_const(tbl, t, &x0, &a0) &&
      term_kind(tbl, x0) == UNINTERPRETED_TERM) {
    assert(is_pos_term(x0));
    *x = x0;
    *a = a0;
    return true;
  }

  return false;
}



/*******************************
 *  UNIT-TYPE REPRESENTATIVES  *
 ******************************/

/*
 * Representative of a singleton type tau:
 * - for scalar type: the unique constant of that type
 * - for function type: an uninterpreted term (denoting the constant function)
 * - for tuple type: (tau_1 ... tau_n)
 *   representative = (tuple (rep tau_1) ... (rep tau_n))
 */

/*
 * Tuple of representative terms.
 */
static term_t make_tuple_rep(term_table_t *table, tuple_type_t *d) {
  term_t aux[8];
  term_t *a;
  term_t t;
  uint32_t i, n;

  n = d->nelem;
  a = aux;
  if (n > 8) {
    a = (term_t *) safe_malloc(n * sizeof(term_t));
  }

  for (i=0; i<n; i++) {
    a[i] = get_unit_type_rep(table, d->elem[i]);
  }
  t = tuple_term(table, n, a);

  if (n > 8) {
    safe_free(a);
  }

  return t;
}

/*
 * Return the term representative for unit type tau.
 * - search the table of unit-types first
 * - create a new term if there's no entry for tau in that table.
 */
term_t get_unit_type_rep(term_table_t *table, type_t tau) {
  type_table_t *types;
  term_t t;

  assert(is_unit_type(table->types, tau));

  t = unit_type_rep(table, tau);
  if (t == NULL_TERM) {
    types = table->types;
    switch (type_kind(types, tau)) {
    case SCALAR_TYPE:
      assert(scalar_type_cardinal(types, tau) == 1);
      t = constant_term(table, tau, 0);
      break;

    case TUPLE_TYPE:
      t = make_tuple_rep(table, tuple_type_desc(types, tau));
      break;

    case FUNCTION_TYPE:
      t = new_uninterpreted_term(table, tau);
      break;

    default:
      assert(false);
      break;
    }
    add_unit_type_rep(table, tau, t);
  }

  return t;
}



/**************
 * VARIABLES  *
 *************/

/*
 * Clone variable v:
 * - v must be a variable
 * - return a fresh variable with the same type as v
 * - if v has a basename, then the clone also gets that name
 */
term_t clone_variable(term_table_t *table, term_t v) {
  type_t tau;
  term_t x;
  char *name;

  assert(term_kind(table, v) == VARIABLE);

  tau = term_type(table, v);
  x = new_variable(table, tau);
  name = term_name(table, v);
  if (name != NULL) {
    set_term_base_name(table, x, name);
  }

  return x;
}


/*
 * Convert variable v to an uninterpreted term
 * - v must be a variable
 * - create a fresh uninterpreted term with the same type as v
 * - if v has a basename, then the clone also gets that name
 */
term_t variable_to_unint(term_table_t *table, term_t v) {
  type_t tau;
  term_t x;
  char *name;

  assert(term_kind(table, v) == VARIABLE);

  tau = term_type(table, v);
  x = new_uninterpreted_term(table, tau);
  name = term_name(table, v);
  if (name != NULL) {
    set_term_base_name(table, x, name);
  }

  return x;
}


