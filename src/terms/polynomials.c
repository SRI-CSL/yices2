/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * POLYNOMIALS
 */

/*
 * Polynomials are sums of monomials.
 * Each monomial is a pair <coeff, variable>.
 * - coeff is a rational number
 * - variable is a 32bit signed integer.
 *
 * This module provides a more compact representation
 * than arith_buffers: polynomials are stored as arrays
 * of monomials.
 */

#include <assert.h>

#include "utils/prng.h"
#include "utils/hash_functions.h"
#include "terms/polynomials.h"


/*********************
 *  MONOMIAL ARRAYS  *
 ********************/

/*
 * Allocate and initialize and array of monomials.
 */
monomial_t *alloc_monarray(uint32_t n) {
  monomial_t *tmp;
  uint32_t i;

  if (n >= MAX_POLY_SIZE) {
    out_of_memory();
  }

  tmp = (monomial_t *) safe_malloc(n * sizeof(monomial_t));
  for (i=0; i<n; i++) {
    q_init(&tmp[i].coeff);
  }

  return tmp;
}

/*
 * Clear all the rationals coefficients
 */
void clear_monarray(monomial_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) q_clear(&a[i].coeff);
}


/*
 * Extend to new size, n = current size.
 */
monomial_t *realloc_monarray(monomial_t *a, uint32_t n, uint32_t new_size) {
  monomial_t *tmp;
  uint32_t i;

  if (new_size <= n) return a;

  if (new_size >= MAX_POLY_SIZE) {
    out_of_memory();
  }

  tmp = (monomial_t *) safe_realloc(a, new_size * sizeof(monomial_t));
  for (i=n; i<new_size; i++) {
    q_init(&tmp[i].coeff);
  }

  return tmp;
}


/*
 * SORT: DEFAULT ORDERING
 */

/*
 * Quick sort array a[low .. high-1]
 * - high - low must be larger than 1
 * - a[high] must exist and have a larger index that all monomials in a[low ... high-1]
 * - sorting cannot cause memory leaks so we don't use the assignment or swap functions
 *   from rationals.h.
 */
static void quick_sort_monarray(monomial_t *a, uint32_t low, uint32_t high) {
  uint32_t i, j, p;
  monomial_t pivot, aux;

  assert(high - low > 1);

  // random pivot
  i =  low + random_uint(high - low);
  assert(low <= i && i < high);
  pivot = a[i];
  p = pivot.var;

  // move pivot into a[low]
  a[i] = a[low];
  a[low] = pivot;

  i = low;
  j = high;
  for (;;) {
    do { j--; } while (p < a[j].var);
    do { i++; } while (p > a[i].var);
    if (i >= j) break;

    // swap a[i] and a[j]
    aux = a[i]; a[i] = a[j]; a[j] = aux;
  }

  // swap a[j] and a[low] = pivot
  a[low] = a[j];
  a[j] = pivot;

  if (j > low + 1) quick_sort_monarray(a, low, j);
  j ++;
  if (high > j + 1) quick_sort_monarray(a, j, high);
}


/*
 * Top-level call to simple sort:
 * - n = size of a minus the end-marker
 * - we must have a[n].var = max_idx
 */
void sort_monarray(monomial_t *a, uint32_t n) {
  assert(a[n].var == max_idx);
  if (n <= 1) return;
  quick_sort_monarray(a, 0, n);
}


/*
 * SORT: CUSTOM ORDERING
 */

/*
 * cmp(data, x, y) defines the ordering, where data is a pointer provided by the caller.
 * - cmp(aux, x, y) must return true if x < y.
 *
 * The ordering must satisfy the following constraints:
 * - const_idx is smaller than any other variable
 * - max_idx is larger than any other variable
 */

/*
 * Quick sort:
 * - preconditions: high - low > 1
 * - a[high] exists and is at least as large as all elements in a[low ... high-1].
 * - sorting cannot cause memory leaks so we don't use the assignment or swap functions
 *   from rationals.h
 */
static void quick_sort_monarray2(monomial_t *a, void *data, var_cmp_fun_t cmp,
                                 uint32_t low, uint32_t high) {
  uint32_t i, j, p;
  monomial_t pivot, aux;

  assert(high - low > 1);

  // random pivot
  i = low + random_uint(high - low);
  assert(low <= i && i < high);
  pivot = a[i];
  p = pivot.var;

  // swap pivot and a[low]
  a[i] = a[low];
  a[low] = pivot;

  i = low;
  j = high;
  for (;;) {
    do { j--; } while (cmp(data, p, a[j].var));
    do { i++; } while (cmp(data, a[i].var, p));
    if (i >= j) break;
    // swap a[i] and a[j]
    aux = a[i]; a[i] = a[j]; a[j] = aux;
  }

  // swap a[j] and a[low] = pivot
  a[low] = a[j];
  a[j] = pivot;

  if (j > low + 1) quick_sort_monarray2(a, data, cmp, low, j);
  j ++;
  if (high > j + 1) quick_sort_monarray2(a, data, cmp, j, high);
}


/*
 * Top-level sort function: n = size of a.
 * a must be terminated by the end marker, i.e., a[n].var = max_idx.
 */
void sort_monarray2(monomial_t *a, uint32_t n, void *data, var_cmp_fun_t cmp) {
  if (n <= 1) return;
  quick_sort_monarray2(a, data, cmp, 0, n);
}



/*
 * NORMALIZATION
 */

/*
 * Normalize an array of monomials a or size n:
 * 1) merge monomials with identical variables:
 *     (c * v + d * v) --> (c + d) * v
 * 2) remove monomials with zero coefficients
 * 3) add end marker.
 * - a must be sorted.
 * - the function returns the size of the result = number of monomials
 *   in a after normalization.
 */
uint32_t normalize_monarray(monomial_t *a, uint32_t n) {
  uint32_t i, j, v;
  rational_t c;

  if (n == 0) return n;

  j = 0;
  q_init(&c);
  v = a[0].var;

  // c := a[0].coeff, clear a[0].coeff to prevent memory leak
  q_copy_and_clear(&c, &a[0].coeff);

  for (i=1; i<n; i++) {
    if (a[i].var == v) {
      q_add(&c, &a[i].coeff);
      q_clear(&a[i].coeff);
    } else {
      if (q_is_nonzero(&c)) {
        a[j].var = v;
        // copy c into a[j].coeff, then clear c
        q_copy_and_clear(&a[j].coeff, &c);
        j ++;
      }
      v = a[i].var;
      // copy a[i].coeff in c then clear a[i].coeff
      q_copy_and_clear(&c, &a[i].coeff);
    }
  }

  if (q_is_nonzero(&c)) {
    a[j].var = v;
    q_copy_and_clear(&a[j].coeff, &c);
    j ++;
  }

  // set end-marker
  a[j].var = max_idx;

  return j;
}





/*
 * OPERATION/COMPARISON
 */

/*
 * Get the constant term of p and copy it in c
 * - p must be normalized
 */
void monarray_constant(monomial_t *p, rational_t *c) {
  if (p->var == const_idx) {
    q_set(c, &p->coeff);
  } else {
    q_clear(c);
  }
}


/*
 * Negate all coefficients
 * - p must be terminated by max_idx.
 */
void in_place_negate_monarray(monomial_t *p) {
  int32_t v;

  v = p->var;
  while (v != max_idx) {
    q_neg(&p->coeff);
    p ++ ;
    v = p->var;
  }
}


/*
 * Copy p into q:
 * - p must be terminated by the end marked
 * - q must be large enough to store the result (including end marker)
 */
uint32_t copy_monarray(monomial_t *p, monomial_t *p1) {
  uint32_t n;
  int32_t v;

  v = p1->var;
  n = 0;
  while (v != max_idx) {
    p->var = v;
    q_set(&p->coeff, &p1->coeff);
    n ++;
    p ++;
    p1 ++;
    v = p1->var;
  }

  p->var = max_idx;

  return n;
}


/*
 * Comparison between two monomial_arrays.
 * - p1 and p2 must be normalized.
 */
bool equal_monarrays(monomial_t *p1, monomial_t *p2) {
  int32_t v1, v2;

  v1 = p1->var;
  v2 = p2->var;
  while (v1 == v2) {
    if (v1 == max_idx) return true;
    if (q_neq(&p1->coeff, &p2->coeff)) return false;

    p1++;
    v1 = p1->var;
    p2++;
    v2 = p2->var;
  }

  return false;
}


/*
 * Check whether p1 - p2 is a non-zero constant
 * - p1 and p2 must be normalized.
 */
bool disequal_monarrays(monomial_t *p1, monomial_t *p2) {
  int32_t v1, v2;

  v1 = p1->var;
  v2 = p2->var;
  if ((v1 == const_idx && v2 == const_idx && q_eq(&p1->coeff, &p2->coeff))
      || (v1 != const_idx && v2 != const_idx)) {
    // same constant term (may be zero in both polynomials)
    return false;
  }

  // skip constants
  if (v1 == const_idx) p1++;
  if (v2 == const_idx) p2++;

  // check whether non-constant monomials are equal
  return equal_monarrays(p1, p2);
}

/*
 * Check whether p1 and p2 are opposite
 * - both must be normalized
 */
bool opposite_monarrays(monomial_t *p1, monomial_t *p2) {
  int32_t v1, v2;

  v1 = p1->var;
  v2 = p2->var;
  while (v1 == v2) {
    if (v1 == max_idx) return true;
    if (! q_opposite(&p1->coeff, &p2->coeff)) return false;
    p1 ++;
    v1 = p1->var;
    p2 ++;
    v2 = p2->var;
  }

  return false;
}


/*
 * Hash code
 * - a must be normalized (and terminated by the end marker)
 * - n = number of terms in a (not counting the end marker)
 */
uint32_t hash_monarray(monomial_t *a, uint32_t n) {
  uint32_t h, num, den;

  h = HASH_POLY_SEED + n;
  while (a->var < max_idx) {
    q_hash_decompose(&a->coeff, &num, &den);
    h = jenkins_hash_triple(a->var, num, den, h);
    a ++;
  }

  return h;
}



/*
 * INTEGER ARITHMETIC
 */

/*
 * Phase and period of p
 * - p is c + (a_1/b_1) x_1 + ... + (a_n/b_n) x_n where
 *   a_i/b_i is an irreducible fraction
 * - let D = gcd(a_1,..., a_n) and L = lcm(b_1,...,b_n)
 *   then period = D/L and phase = c - floor(c/period) * period
 */
void monarray_period_and_phase(monomial_t *p, rational_t *period, rational_t *phase) {
  rational_t aux;
  monomial_t *c;
  int32_t v;

  /*
   * c := the constant monomial of p or NULL if p's constant is zero
   */
  c = NULL;
  v = p->var;
  if (v == const_idx) {
    c = p;
    p ++;
    v = p->var;
  }

  if (v < max_idx) {
    /*
     * p is not a constant: compute D and L
     * we use period for D and phase for L
     */
    q_get_num(period, &p->coeff); // D := |a_1|
    if (q_is_neg(period)) {
      q_neg(period);
    }

    q_get_den(phase, &p->coeff);  // L := b_1
    q_init(&aux);

    for (;;) {
      p ++;
      v = p->var;
      if (v >= max_idx) break;
      q_get_num(&aux, &p->coeff);
      q_gcd(period, &aux);        // D := gcd(D, a_i)
      q_get_den(&aux, &p->coeff);
      q_lcm(phase, &aux);         // L := lcm(L, b_i)
    }

    assert(q_is_pos(period) && q_is_pos(phase));
    q_div(period, phase);        // period := D/L

    /*
     * Phase: constant modulo D/L
     */
    if (c == NULL) {
      q_clear(phase);  // no constant: phase = 0
    } else {
      q_set(&aux, &c->coeff);
      q_div(&aux, period);
      q_floor(&aux);             // aux = floor(c/period)
      q_set(phase, &c->coeff);
      q_submul(phase, &aux, period); // phase = c - aux * period

      assert(q_is_nonneg(phase) && q_lt(phase, period));
    }

    q_clear(&aux);

  } else {
    /*
     * p is constant: period := 0, phase = constant coeff
     */
    q_clear(period);
    if (c == NULL) {
      q_clear(phase);
    } else {
      q_set(phase, &c->coeff);
    }
  }

}



/*
 * If p is an integer polynomial, compute factor = gcd of its coefficients
 * - p must be normalized and all its coefficients must be integers
 * - if p is zero, then factor is set to zero
 */
void monarray_common_factor(monomial_t *p, rational_t *factor) {
  int32_t v;

  v = p->var;
  if (v < max_idx) {
    // p is non zero
    assert(q_is_integer(&p->coeff));
    q_set_abs(factor, &p->coeff);
    for (;;) {
      p ++;
      v = p->var;
      if (v >= max_idx) break;
      assert(q_is_integer(&p->coeff));
      q_gcd(factor, &p->coeff);
    }

  } else {
    // p is zero
    q_clear(factor);
  }
}


/*
 * Same thing but skip the constant if there's one
 */
void monarray_gcd(monomial_t *p, rational_t *gcd) {
  if (p->var == const_idx) p ++;
  monarray_common_factor(p, gcd);
}



/*
 * SUPPORT FOR SIMPLIFYING IF-THEN-ELSE
 */

/*
 * Extract the common part of p and q:
 * - p and q must both be normalized
 * - the set of variables x_1, ..., x_k such that
 *   x_i occurs with the same coefficient in p and q is added to vector v.
 * - these variables are in increasing order
 */
void monarray_pair_common_part(monomial_t *p, monomial_t *q, ivector_t *v) {
  int32_t x, y;

  x = p->var;
  y = q->var;
  while (x < max_idx && y < max_idx) {
    if (x < y) {
      p ++;
      x = p->var;
    } else if (y < x) {
      q ++;
      y = q->var;
    } else {
      if (q_eq(&p->coeff, &q->coeff)) {
        ivector_push(v, x);
      }
      p ++;
      x = p->var;
      q ++;
      y = q->var;
    }
  }
}


/*
 * Store gcd(a, b) into a
 * - if a is zero, copy b's absolute value into a
 * - a and b must be integer
 * - b must be non zero
 */
static void aux_gcd(rational_t *a, rational_t *b) {
  assert(q_is_integer(a) && q_is_integer(b));

  if (q_is_zero(a)) {
    q_set_abs(a, b);
  } else {
    q_gcd(a, b);
  }
}

/*
 * Given p and q as above
 * - p and q must be normalized and have integer coefficients
 * - compute the GCD of all coefficients in p and q that are not
 *   in the common part.
 * - the result is returned in factor.
 * - if p = q, then the result is 0
 */
void monarray_pair_non_common_gcd(monomial_t *p, monomial_t *q, rational_t *factor) {
  int32_t x, y;

  q_clear(factor);
  x = p->var;
  y = q->var;
  for (;;) {
    if (x == y) {
      if (x == max_idx) break;
      if (q_neq(&p->coeff, &q->coeff)) {
        // a.x and b.x not in the common part
        aux_gcd(factor, &p->coeff);
        aux_gcd(factor, &q->coeff);
      }
      p ++;
      x = p->var;
      q ++;
      y = q->var;
    } else if (x < y) {
      aux_gcd(factor, &p->coeff);
      p ++;
      x = p->var;
    } else {
      aux_gcd(factor, &q->coeff);
      q ++;
      y = q->var;
    }
  }
}







/*****************
 *  POLYNOMIALS  *
 ****************/

/*
 * Allocate and partially initialize a polynomial of n terms
 * - the rational coefficients are initialized to 0
 * - the variable indices are not initialized, except for the end marker
 */
polynomial_t *alloc_raw_polynomial(uint32_t n) {
  polynomial_t *p;
  uint32_t i;

  if (n >= MAX_POLY_SIZE) {
    out_of_memory();
  }
  p = (polynomial_t *) safe_malloc(sizeof(polynomial_t) + (n + 1) * sizeof(monomial_t));
  p->nterms = n;
  for (i=0; i<n; i++) {
    q_init(&p->mono[i].coeff);
  }
  p->mono[i].var = max_idx;
  q_init(&p->mono[i].coeff);

  return p;
}


/*
 * Allocate a polynomial_t object and copy a into it.
 * - a must be normalized.
 * - side effect: a is reset to 0.
 */
polynomial_t *monarray_get_poly(monomial_t *a, uint32_t n) {
  polynomial_t *p;
  uint32_t i;

  if (n >= MAX_POLY_SIZE) {
    out_of_memory();
  }
  p = (polynomial_t *) safe_malloc(sizeof(polynomial_t) + (n + 1) * sizeof(monomial_t));
  p->nterms = n;
  for (i=0; i<n; i++) {
    p->mono[i].var = a[i].var;
    q_copy_and_clear(&p->mono[i].coeff, &a[i].coeff);
  }
  // end-marker
  p->mono[i].var = max_idx;
  q_init(&p->mono[i].coeff);

  return p;
}


/*
 * Allocate a polynomial_t object and copy a into it.
 * - a must be normalized.
 * - no side effect.
 */
polynomial_t *monarray_copy_to_poly(monomial_t *a, uint32_t n) {
  polynomial_t *p;
  uint32_t i;

  if (n >= MAX_POLY_SIZE) {
    out_of_memory();
  }
  p = (polynomial_t *) safe_malloc(sizeof(polynomial_t) + (n + 1) * sizeof(monomial_t));
  p->nterms = n;
  for (i=0; i<n; i++) {
    p->mono[i].var = a[i].var;
    q_init(&p->mono[i].coeff);
    q_set(&p->mono[i].coeff, &a[i].coeff);
  }
  // end-marker
  p->mono[i].var = max_idx;
  q_init(&p->mono[i].coeff);

  return p;
}


/*
 * Hash code for polynomial p
 * - p must be normalized.
 */
uint32_t hash_polynomial(polynomial_t *p) {
  return hash_monarray(p->mono, p->nterms);
}




/*
 * Maximal variable of p = last variable
 * For p == 0, return null_idx
 */
int32_t polynomial_main_var(polynomial_t *p) {
  uint32_t n;

  n = p->nterms;
  if (n == 0) {
    return null_idx;
  }
  return p->mono[n - 1].var;
}




/*
 * Check whether p is constant.
 * - p must be normalized
 */
bool polynomial_is_constant(polynomial_t *p) {
  return p->nterms == 0 || (p->nterms == 1 && p->mono[0].var == const_idx);
}


/*
 * Check whether p is constant and nonzero
 * - p must be normalized
 */
bool polynomial_is_nonzero(polynomial_t *p) {
  return p->nterms == 1 && p->mono[0].var == const_idx;
}


/*
 * Check whether p is constant and positive, negative, etc.
 * These checks are incomplete (but cheap). They always return
 * false if p is non-constant.
 */
bool polynomial_is_pos(polynomial_t *p) {
  return p->nterms == 1 && p->mono[0].var == const_idx
    && q_is_pos(&p->mono[0].coeff);
}

bool polynomial_is_neg(polynomial_t *p) {
  return p->nterms == 1 && p->mono[0].var == const_idx
    && q_is_neg(&p->mono[0].coeff);
}

bool polynomial_is_nonneg(polynomial_t *p) {
  return p->nterms == 0 ||
    (p->nterms == 1 && p->mono[0].var == const_idx
     && q_is_pos(&p->mono[0].coeff));
}

bool polynomial_is_nonpos(polynomial_t *p) {
  return p->nterms == 0 ||
    (p->nterms == 1 && p->mono[0].var == const_idx
     && q_is_neg(&p->mono[0].coeff));
}


/*
 * Check whether p == k + x for non-zero k and variable x
 */
bool polynomial_is_const_plus_var(polynomial_t *p, int32_t x) {
  return p->nterms == 2 && p->mono[0].var == const_idx && p->mono[1].var == x
    && q_is_one(&p->mono[1].coeff);
}

/*
 * Check whether p == x for variable x
 */
bool polynomial_is_var(polynomial_t *p, int32_t x) {
  return p->nterms == 1 && p->mono[0].var == x && q_is_one(&p->mono[0].coeff);
}

