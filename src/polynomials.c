/*
 * Polynomials: represented as sums of monomials
 *
 * All polynomials are attached to a manager that keeps
 * track of the variables and monomial ids.
 */

#include "memalloc.h"
#include "polynomials.h"
#include "hash_functions.h"


// seed used in hash functions.
#define HASH_SEED 0x9327a7bf



/*********************
 *  MONOMIAL ARRAYS  *
 ********************/

/*
 * Allocate and initialize and array of monomials.
 */
monomial_t *alloc_monarray(int32_t n) {
  monomial_t *tmp;
  int32_t i;

  assert(0 <= n && n < MAX_POLY_SIZE);
  tmp = (monomial_t *) safe_malloc(n * sizeof(monomial_t));
  for (i=0; i<n; i++) {
    q_init(&tmp[i].coeff);
  }

  return tmp;
}

/*
 * Clear all the rationals coefficients
 */
void clear_monarray(monomial_t *a, int32_t n) {
  int32_t i;

  for (i=0; i<n; i++) q_clear(&a[i].coeff);
}


/*
 * Extend to new size, n = current size.
 */
monomial_t *realloc_monarray(monomial_t *a, int32_t n, int32_t new_size) {
  monomial_t *tmp;
  int32_t i;

  if (new_size <= n) return a;

  assert(new_size < MAX_POLY_SIZE);
  tmp = (monomial_t *) safe_realloc(a, new_size * sizeof(monomial_t));
  for (i=n; i<new_size; i++) {
    q_init(&tmp[i].coeff);
  }

  return tmp;
}


/*
 * Allocate and partially initialize a polyomial of n terms
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
 * quick sort: assumes a[high] exists and is at least as large as all elements in a[low ... high-1].
 * also assumes high - low > 1
 * - sorting cannot cause memory leaks so we don't use the assignment or swap functions
 *   from rationals.h 
 */
static void quick_sort_monarray(arithvar_manager_t *m, monomial_t *a, int32_t low, int32_t high) {
  int32_t i, j, p;
  monomial_t pivot, aux;
  polynomial_manager_t *pm;

  assert(high - low > 1);

  pm = &m->pm;
  // TODO: choose a random pivot?
  pivot = a[low];
  p = pivot.var;
  i = low;
  j = high;
  for (;;) {
    do { j--; } while (polymanager_var_precedes(pm, p, a[j].var));
    do { i++; } while (polymanager_var_precedes(pm, a[i].var, p));
    if (i >= j) break;
    // swap a[i] and a[j]
    aux = a[i]; a[i] = a[j]; a[j] = aux;
  }

  // swap a[j] and a[low] = pivot
  a[low] = a[j];
  a[j] = pivot;

  if (j > low + 1) quick_sort_monarray(m, a, low, j);
  j ++;
  if (high > j + 1) quick_sort_monarray(m, a, j, high);
}


/*
 * top-level sort function: n = size of a. 
 * a must be terminated by the end marker, i.e., a[n].var = max_idx. 
 */
void sort_monarray(arithvar_manager_t *m, monomial_t *a, int32_t n) {
  if (n <= 1) return;
  quick_sort_monarray(m, a, 0, n);
}



/*
 * Simple sort: don't use a manager, just sort in increasing order of variables
 * The preconditions are the same as above for quick_sort: 
 * - a[high] exists and is at least as large as all elements in a[low ... high-1]
 * - high - low > 1
 */
static void simple_quick_sort_monarray(monomial_t *a, int32_t low, int32_t high) {
  int32_t i, j, p;
  monomial_t pivot, aux;

  assert(high - low > 1);

  pivot = a[low];
  p = pivot.var;
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

  if (j > low + 1) simple_quick_sort_monarray(a, low, j);
  j ++;
  if (high > j + 1) simple_quick_sort_monarray(a, j, high);
}


/*
 * Top-level call to simple sort: n = size of a minus the end-marker
 * we must have a[n].var = max_idx
 */
void varsort_monarray(monomial_t *a, int32_t n) {
  assert(n >= 0 && a[n].var == max_idx);
  if (n <= 1) return;
  simple_quick_sort_monarray(a, 0, n);
}



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
int32_t normalize_monarray(monomial_t *a, int32_t n) {
  int32_t i, j, v;
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
 * Allocate a polynomial_t object and copy a into it.
 * - a must be normalized.
 * - side effect: a is reset to 0.
 */
polynomial_t *monarray_getpoly(monomial_t *a, int32_t n) {
  polynomial_t *p;
  int32_t i;

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
polynomial_t *monarray_copy(monomial_t *a, int32_t n) {
  polynomial_t *p;
  int32_t i;

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
 * Comparison between two monomial_arrays.
 * - p1 and p2 must be normalized, terminated by max_idx
 */
bool equal_monarray(monomial_t *p1, monomial_t *p2) {
  arith_var_t v1, v2;

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
 */
bool must_disequal_monarray(monomial_t *p1, monomial_t *p2) {
  arith_var_t v1, v2;

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
  return equal_monarray(p1, p2);
}



/*
 * Hash code for polynomial p
 * - p must be normalized.
 */
uint32_t hash_monarray(monomial_t *p) {
  arith_var_t v;
  uint32_t h, hn, hd;

  h = HASH_SEED;
  v = p->var;
  while (v < max_idx) {
    q_hash_decompose(&p->coeff, &hn, &hd);
    h = jenkins_hash_triple(v, hn, hd, h);

    p ++;
    v = p->var;
  }
  return h;
}


/*
 * Check whether all variables and coefficients in p are integer
 * - p must be normalized and all variables must be declared in m
 */
bool is_int_monarray(monomial_t *p, arithvar_manager_t *m) {
  arith_var_t v;

  v = p->var;
  while (v < max_idx) {
    if (! arithvar_manager_var_is_int(m, v)) return false;
    if (! q_is_integer(&p->coeff)) return false;
    p ++;
    v = p->var;
  }

  return true;
}


/*
 * Check whether all variables of p are integer
 * - p must be normalized and all variables must be declared in m
 */
bool all_integer_vars_in_monarray(monomial_t *p, arithvar_manager_t *m) {
  arith_var_t v;

  v = p->var;
  while (v < max_idx) {
    if (! arithvar_manager_var_is_int(m, v)) return false;
    p ++;
    v = p->var;
  }
  return true;  
}




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
  arith_var_t v;

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
  arith_var_t v;

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
 * Operations
 *
 *  copy: p := p1
 *  negate: p := -p1
 *  mul_const: p := a * p1
 *  add: p := p1 + p2
 *  sub: p := p1 - p2
 *  addmul_const: p = p1 + a * p2
 *  addmul_const: p = p1 - a * p2
 * 
 * - the arguments p1 and p2 must be normalized.
 * - rational a must be non-zero.
 * - p must be large enough to store the result
 * - p must not overlap with p1 or p2
 * - all coefficients of p must be initialized (via q_init).
 * - all functions return the size of the result = 
 *   number of monomials, not including the end marker.
 */
int32_t copy_monarray(monomial_t *p, monomial_t *p1) {
  int32_t n, v;

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

int32_t negate_monarray(monomial_t *p, monomial_t *p1) {
  int32_t n, v;

  v = p1->var;
  n = 0;
  while (v != max_idx) {
    p->var = v;
    q_set_neg(&p->coeff, &p1->coeff);
    n ++;
    p ++;
    p1 ++;
    v = p1->var;
  }

  p->var = max_idx;

  return n;
}

int32_t mul_const_monarray(monomial_t *p, monomial_t *p1, rational_t *a) {
  int32_t n, v;

  assert(q_is_nonzero(a));

  v = p1->var;
  n = 0;
  while (v != max_idx) {
    p->var = v;
    q_set(&p->coeff, &p1->coeff);
    q_mul(&p->coeff, a);
    n ++;
    p ++;
    p1 ++;
    v = p1->var;
  }

  p->var = max_idx;

  return n;  
}

int32_t mul_var_monarray(monomial_t *p, monomial_t *p1, arith_var_t v, arithvar_manager_t *m) {
  int32_t n, v1;

  v1 = p1->var;
  n = 0;
  while (v1 != max_idx) {
    p->var = arithvar_manager_mul_var(m, v1, v);
    q_set(&p->coeff, &p1->coeff);
    n ++;
    p ++;
    p1 ++;
    v = p1->var;
  }

  p->var = max_idx;

  return n;
}

int32_t mul_negvar_monarray(monomial_t *p, monomial_t *p1, arith_var_t v, arithvar_manager_t *m) {
  int32_t n, v1;

  v1 = p1->var;
  n = 0;
  while (v1 != max_idx) {
    p->var = arithvar_manager_mul_var(m, v1, v);
    q_set_neg(&p->coeff, &p1->coeff);
    n ++;
    p ++;
    p1 ++;
    v = p1->var;
  }

  p->var = max_idx;

  return n;
}

int32_t mul_mono_monarray(monomial_t *p, monomial_t *p1, arith_var_t v, rational_t *a, arithvar_manager_t *m) {
  int32_t n, v1;

  assert(q_is_nonzero(a));
  
  v1 = p1->var;
  n = 0;
  while (v1 != max_idx) {
    p->var = arithvar_manager_mul_var(m, v1, v);
    q_set(&p->coeff, &p1->coeff);
    q_mul(&p->coeff, a);
    n ++;
    p ++;
    p1 ++;
    v = p1->var;
  }

  p->var = max_idx;

  return n;
}

int32_t add_monarrays(monomial_t *p, monomial_t *p1, monomial_t *p2) {
  int32_t n, v1, v2;
  rational_t c;

  q_init(&c);
  n = 0;
  v1 = p1->var;
  v2 = p2->var;

  for (;;) {
    if (v1 == v2) {
      if (v1 == max_idx) break;

      q_set(&c, &p1->coeff);
      q_add(&c, &p2->coeff);
      if (q_is_nonzero(&c)) {
	p->var = v1;
	q_copy_and_clear(&p->coeff, &c);
	n ++;
	p ++;
      }
      p1 ++;
      v1 = p1->var;
      p2 ++;
      v2 = p2->var;
      
    } else if (v1 < v2) {
      p->var = v1;
      q_set(&p->coeff, &p1->coeff);
      n ++;
      p ++;
      p1 ++;
      v1 = p1->var;

    } else {
      p->var = v2;
      q_set(&p->coeff, &p2->coeff);
      n ++;
      p ++;
      p2 ++;
      v2 = p2->var;
    }
  }

  p->var = max_idx;

  return n;
}

int32_t sub_monarrays(monomial_t *p, monomial_t *p1, monomial_t *p2) {
  int32_t n, v1, v2;
  rational_t c;

  q_init(&c);
  n = 0;
  v1 = p1->var;
  v2 = p2->var;

  for (;;) {
    if (v1 == v2) {
      if (v1 == max_idx) break;

      q_set(&c, &p1->coeff);
      q_sub(&c, &p2->coeff);
      if (q_is_nonzero(&c)) {
	p->var = v1;
	q_copy_and_clear(&p->coeff, &c);
	n ++;
	p ++;
      }
      p1 ++;
      v1 = p1->var;
      p2 ++;
      v2 = p2->var;
      
    } else if (v1 < v2) {
      p->var = v1;
      q_set(&p->coeff, &p1->coeff);
      n ++;
      p ++;
      p1 ++;
      v1 = p1->var;

    } else {
      p->var = v2;
      q_set_neg(&p->coeff, &p2->coeff);
      n ++;
      p ++;
      p2 ++;
      v2 = p2->var;
    }
  }

  p->var = max_idx;

  return n;
}

int32_t addmul_const_monarrays(monomial_t *p, monomial_t *p1, monomial_t *p2, rational_t *a) {
  int32_t n, v1, v2;
  rational_t c;

  assert(q_is_nonzero(a));

  q_init(&c);
  n = 0;
  v1 = p1->var;
  v2 = p2->var;

  for (;;) {
    if (v1 == v2) {
      if (v1 == max_idx) break;

      q_set(&c, &p1->coeff);
      q_addmul(&c, &p2->coeff, a);
      if (q_is_nonzero(&c)) {
	p->var = v1;
	q_copy_and_clear(&p->coeff, &c);
	n ++;
	p ++;
      }
      p1 ++;
      v1 = p1->var;
      p2 ++;
      v2 = p2->var;
      
    } else if (v1 < v2) {
      p->var = v1;
      q_set(&p->coeff, &p1->coeff);
      n ++;
      p ++;
      p1 ++;
      v1 = p1->var;

    } else {
      p->var = v2;
      q_set(&p->coeff, &p2->coeff);
      q_mul(&p->coeff, a);
      n ++;
      p ++;
      p2 ++;
      v2 = p2->var;
    }
  }

  p->var = max_idx;

  return n;
}

int32_t submul_const_monarrays(monomial_t *p, monomial_t *p1, monomial_t *p2, rational_t *a) {
  int32_t n, v1, v2;
  rational_t c;

  assert(q_is_nonzero(a));

  q_init(&c);
  n = 0;
  v1 = p1->var;
  v2 = p2->var;

  for (;;) {
    if (v1 == v2) {
      if (v1 == max_idx) break;

      q_set(&c, &p1->coeff);
      q_submul(&c, &p2->coeff, a);
      if (q_is_nonzero(&c)) {
	p->var = v1;
	q_copy_and_clear(&p->coeff, &c);
	n ++;
	p ++;
      }
      p1 ++;
      v1 = p1->var;
      p2 ++;
      v2 = p2->var;
      
    } else if (v1 < v2) {
      p->var = v1;
      q_set(&p->coeff, &p1->coeff);
      n ++;
      p ++;
      p1 ++;
      v1 = p1->var;

    } else {
      p->var = v2;
      q_set_neg(&p->coeff, &p2->coeff);
      q_mul(&p->coeff, a);
      n ++;
      p ++;
      p2 ++;
      v2 = p2->var;
    }
  }

  p->var = max_idx;

  return n;
}


/*
 * In-place operations should be faster
 * - p must be normalized
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

void in_place_mul_const_monarray(monomial_t *p, rational_t *a) {
  int32_t v;

  assert(q_is_nonzero(a));

  v = p->var;
  while (v != max_idx) {
    q_mul(&p->coeff, a);
    p ++ ;
    v = p->var;
  }
}

// multiply p by v
void in_place_mul_var_monarray(monomial_t *p, arith_var_t v, arithvar_manager_t *m) {
  arith_var_t v1;

  v1 = p->var;
  while (v1 != max_idx) {
    p->var = arithvar_manager_mul_var(m, v1, v);
    p ++;
    v1 = p->var;
  }
}

// multiply by -v
void in_place_mul_negvar_monarray(monomial_t *p, arith_var_t v, arithvar_manager_t *m) {
  arith_var_t v1;

  v1 = p->var;
  while (v1 != max_idx) {
    p->var = arithvar_manager_mul_var(m, v1, v);
    q_neg(&p->coeff);
    p ++;
    v1 = p->var;
  }
}

// multiply p by a * v.
void in_place_mul_mono_monarray(monomial_t *p, arith_var_t v, rational_t *a, arithvar_manager_t *m) {
  arith_var_t v1;

  assert(q_is_nonzero(a));

  v1 = p->var;
  while (v1 != max_idx) {
    p->var = arithvar_manager_mul_var(m, v1, v);
    q_mul(&p->coeff, a);
    p ++;
    v1 = p->var;
  }
}



/******************************************
 *  AUXILIARY OPERATIONS ON POLYNOMIALS   *
 *****************************************/

/*
 * Maximal variable of p (in lexical ordering).
 * For p == 0, return null_idx
 */
arith_var_t polynomial_main_var(polynomial_t *p) {
  int32_t n;
  n = p->nterms;
  if (n == 0) {
    return null_idx;
  }
  return p->mono[n - 1].var;
}


/*
 * Degree of p.
 * - If p is zero, returns 0.
 */
int32_t polynomial_degree(polynomial_t *p, arithvar_manager_t *m) {
  arith_var_t v;

  v = polynomial_main_var(p);
  if (v == null_idx) {
    return 0;
  }
  return polymanager_var_degree(&m->pm, v);
}



/*
 * Compute the degree of variable x in p
 * - m = variable manager for the variables of p
 * - x must be a primitive variable in m
 */
int32_t polynomial_var_degree(polynomial_t *p, arithvar_manager_t *m, arith_var_t x) {
  int32_t i, n, d, k;

  assert(arithvar_manager_var_is_primitive(m, x));

  d = 0;
  n = p->nterms;
  for (i=0; i<n; i++) {
    assert(q_is_nonzero(&p->mono[i].coeff));
    k = arithvar_manager_var_degree_in_prod(m, p->mono[i].var, x);
    if (k > d) {
      d = k;
    }
  }

  return d;
}


/*
 * Store all variables of p in vector u
 */
void polynomial_get_vars(polynomial_t *p, arithvar_manager_t *m, ivector_t *u) {
  int32_t i, n;

  ivector_reset(u);
  n = p->nterms;
  for (i=0; i<n; i++) {
    arithvar_manager_get_vars(m, p->mono[i].var, u); 
  }
  ivector_remove_duplicates(u);
}


/*
 * Store the terms attached to variables of p in vector u
 */
void polynomial_get_terms(polynomial_t *p, arithvar_manager_t *m, ivector_t *u) {
  int32_t i, n;

  ivector_reset(u);
  n = p->nterms;
  for (i=0; i<n; i++) {
    arithvar_manager_get_terms(m, p->mono[i].var, u); 
  }
  ivector_remove_duplicates(u);
}



/**********************
 * POLYNOMIAL BUFFERS *
 *********************/

/*
 * Initialize store s
 */
void init_mlist_store(object_store_t *s) {
  init_objstore(s, sizeof(mlist_t), MLIST_BANK_SIZE);
}

/*
 * Delete store s
 */
static void finalizer(void *l) {
  q_clear(&((mlist_t *) l)->coeff);
}

void delete_mlist_store(object_store_t *s) {
  objstore_delete_finalize(s, finalizer);
}

/*
 * Allocate a list element in s
 */
static inline mlist_t *alloc_list_elem(object_store_t *s) {
  mlist_t *tmp = (mlist_t *) objstore_alloc(s);
  q_init(&tmp->coeff);
  return tmp;
}


/*
 * Free list element l
 */
static inline void free_list_elem(object_store_t *s, mlist_t *l) {
  objstore_free(s, l);
}



/*
 * Initialize buffer b to zero and allocate internal buffers.
 * - m = attached manager. 
 * - s = attached store.
 * All variables occurring in b must be defined in m.
 */
void init_arith_buffer(arith_buffer_t *b, arithvar_manager_t *m, object_store_t *s) {
  mlist_t *start, *end;

  b->nterms = 0;
  b->store = s;
  b->manager = m;

  // end marker
  end = alloc_list_elem(s);
  end->next = NULL;
  end->var = max_idx;

  // first element: start marker
  start = alloc_list_elem(s);
  start->next = end;
  start->var = null_idx; // -1  

  b->list = start;
}


/*
 * Delete b and free all attached memory
 */
void delete_arith_buffer(arith_buffer_t *b) {
  mlist_t *l, *next;

  l = b->list->next;
  while (l->var < max_idx) {
    next = l->next;
    q_clear(&l->coeff); // ?? not necessary.
    free_list_elem(b->store, l);
    l = next;
  }

  b->store = NULL;
  b->manager = NULL;
  b->list = NULL;
}



/*
 * Normalize: remove any zero monomials from b
 */
void arith_buffer_normalize(arith_buffer_t *b) {
  mlist_t *p, *q;

  q = b->list;
  p = q->next;
  while (p->var < max_idx) {
    if (q_is_zero(&p->coeff)) {
      q->next = p->next;
      free_list_elem(b->store, p);
      b->nterms --;
      p = q->next;
    } else {
      q = p;
      p = q->next;
    }
  }  
}


/*
 * Reset buffer: empty the list
 */
void arith_buffer_reset(arith_buffer_t *b) {
  mlist_t *p, *q, *start;

  if (b->nterms == 0) return;

  start = b->list;
  p = start->next;
  while (p->var < max_idx) {
    q = p->next;    
    q_clear(&p->coeff);    
    free_list_elem(b->store, p);
    p = q;
  }

  assert(p->var == max_idx);
  start->next = p;
  b->nterms = 0;
}


/*
 * Construct a polynomial_t object out of b.
 * - b must be normalized.
 * - SIDE EFFECT: b is reset.
 */
polynomial_t *arith_buffer_getpoly(arith_buffer_t *b) {
  mlist_t *q, *next;
  polynomial_t *p;
  int32_t i, n;

  n = b->nterms;
  p = (polynomial_t *) safe_malloc(sizeof(polynomial_t) + (n + 1) * sizeof(monomial_t));
  p->nterms = n;

  q = b->list->next;
  i = 0;
  while (q->var < max_idx) {
    assert(q_is_nonzero(&q->coeff));
    p->mono[i].var = q->var;
    q_copy_and_clear(&p->mono[i].coeff, &q->coeff);
    // free element q from the list
    next = q->next;
    free_list_elem(b->store, q);
    q = next;
    i ++;
  }

  b->list->next = q;
  b->nterms = 0;

  p->mono[i].var = max_idx;
  q_init(&p->mono[i].coeff);

  return p;
}


/*
 * Main variable = last in the list
 */
arith_var_t arith_buffer_main_variable(arith_buffer_t *b) {
  mlist_t *p;
  arith_var_t v;

  p = b->list;
  do {
    v = p->var;
    p = p->next;
  } while (p->var < max_idx);

  return v;
}


/*
 * Degree: returns 0 if b is null.
 */
int32_t arith_buffer_degree(arith_buffer_t *b) {
  arith_var_t v;

  v = arith_buffer_main_variable(b);
  if (v == null_idx) return 0;
  return polymanager_var_degree(&b->manager->pm, v);
}


/*
 * Degree of variable x in b.
 * - x must be a primitive variable in b's variable manager
 * - return 0 if x does not occur in b
 */
int32_t arith_buffer_var_degree(arith_buffer_t *b, arith_var_t x) {
  arithvar_manager_t *m;
  mlist_t *p;
  int32_t d, k;

  assert(arithvar_manager_var_is_primitive(b->manager, x));

  m = b->manager;
  p = b->list->next;
  d = 0;
  while (p->var < max_idx) {
    if (q_is_nonzero(&p->coeff)) {
      k = arithvar_manager_var_degree_in_prod(m, p->var, x);
      if (k > d) {
	d = k;
      }
    }
  }

  return d;
}



/*
 * Hash code for buffer b
 * - b must be normalized.
 */
uint32_t arith_buffer_hash(arith_buffer_t *b) {
  mlist_t *p;
  arith_var_t v;
  uint32_t h, hn, hd;

  h = HASH_SEED;
  p = b->list->next;
  v = p->var;
  while (v < max_idx) {
    q_hash_decompose(&p->coeff, &hn, &hd);
    h = jenkins_hash_triple(v, hn, hd, h);
    p = p->next;
    v = p->var;
  }

  return h;
}


/*
 * Check whether all variables and coefficients in b are integer
 * - b must be normalized
 */
bool arith_buffer_is_int(arith_buffer_t *b) {
  mlist_t *p;
  arith_var_t v;
  arithvar_manager_t *m;

  m = b->manager;
  p = b->list->next;
  v = p->var;
  while (v < max_idx) {
    if (! arithvar_manager_var_is_int(m, v)) return false;
    if (! q_is_integer(&p->coeff)) return false;
    p = p->next;
    v = p->var;
  }

  return true;
}

/*
 * Check whether b == k + x for non-zero k and variable x
 * - b must be normalized
 */
bool arith_buffer_is_const_plus_var(arith_buffer_t *b, arith_var_t x) {
  mlist_t *p;

  if (b->nterms == 2) {
    p = b->list->next;
    return p->var == const_idx && p->next->var == x && q_is_one(&p->next->coeff);
  }

  return false;
}


/*
 * Check whether b is of the form a * (x - y) for two primitive variables x and y
 * - b must be normalized
 */
bool arith_buffer_is_equality(arith_buffer_t *b, arith_var_t *x, arith_var_t *y) {
  mlist_t *p;
  arith_var_t xx, yy;
  rational_t a;
  bool is_eq;

  is_eq = false;

  if (b->nterms == 2) {
    p = b->list->next;
    xx = p->var;
    yy = p->next->var;
    if (arithvar_manager_var_is_primitive(b->manager, xx) &&
	arithvar_manager_var_is_primitive(b->manager, yy)) {
      *x = xx;
      *y = yy;
      q_init(&a);
      q_set(&a, &p->coeff);
      q_add(&a, &p->next->coeff);
      is_eq = q_is_zero(&a);
      q_clear(&a);
    }
  }

  return is_eq;
}


/*
 * Compute opposite of b.
 */
void arith_buffer_negate(arith_buffer_t *b) {
  mlist_t *p;
  arith_var_t v;

  p = b->list->next;
  v = p->var;
  while (v < max_idx) {
    q_neg(&p->coeff);
    p = p->next;
    v = p->var;
  }  
}

/*
 * Multiply b by v
 */
void arith_buffer_mul_var(arith_buffer_t *b, arith_var_t v) {
  mlist_t *p;
  arith_var_t v1;
  arithvar_manager_t *m;

  assert(polymanager_var_is_valid(&b->manager->pm, v));

  m = b->manager;
  p = b->list->next;
  v1 = p->var;

  while (v1 < max_idx) {
    p->var = arithvar_manager_mul_var(m, v, v1);
    p = p->next;
    v1 = p->var;
  }
}

/*
 * Multiply b by -v
 */
void arith_buffer_mul_negvar(arith_buffer_t *b, arith_var_t v) {
  mlist_t *p;
  arith_var_t v1;
  arithvar_manager_t *m;

  assert(polymanager_var_is_valid(&b->manager->pm, v));

  m = b->manager;
  p = b->list->next;
  v1 = p->var;

  while (v1 < max_idx) {
    p->var = arithvar_manager_mul_var(m, v, v1);
    q_neg(&p->coeff);
    p = p->next;
    v1 = p->var;
  }
}

/*
 * Multiply b by a. a must be nonzero
 */
void arith_buffer_mul_const(arith_buffer_t *b, rational_t *a) {
  mlist_t *p;
  arith_var_t v;

  assert(q_is_nonzero(a));

  p = b->list->next;
  v = p->var;

  while (v < max_idx) {
    q_mul(&p->coeff, a);
    p = p->next;
    v = p->var;
  }
}

/*
 * Divide b by a. a must be nonzero
 */
void arith_buffer_div_const(arith_buffer_t *b, rational_t *a) {
  mlist_t *p;
  arith_var_t v;

  assert(q_is_nonzero(a));

  p = b->list->next;
  v = p->var;

  while (v < max_idx) {
    q_div(&p->coeff, a);
    p = p->next;
    v = p->var;
  }
}


/*
 * Multiply b by a * v. a must be nonzero
 */
void arith_buffer_mul_mono(arith_buffer_t *b, arith_var_t v, rational_t *a) {
  mlist_t *p;
  arith_var_t v1;
  arithvar_manager_t *m;

  assert(polymanager_var_is_valid(&b->manager->pm, v));
  assert(q_is_nonzero(a));

  m = b->manager;
  p = b->list->next;
  v1 = p->var;

  while (v1 < max_idx) {
    p->var = arithvar_manager_mul_var(m, v, v1);
    q_mul(&p->coeff, a);
    p = p->next;
    v1 = p->var;
  }
}


/*
 * Add monomial a * v to b
 */
void arith_buffer_add_mono(arith_buffer_t *b, arith_var_t v, rational_t *a) {
  mlist_t *p, *q, *aux;
  polynomial_manager_t *m;

  assert(polymanager_var_is_valid(&b->manager->pm, v));

  if (q_is_zero(a)) return;

  m = &b->manager->pm;
  p = b->list; // p == start marker (to be skipped)

  do {
    q = p; 
    p = q->next;
  } while (polymanager_var_precedes(m, p->var, v));

  if (p->var == v) {
    q_add(&p->coeff, a);
  } else {
    aux = alloc_list_elem(b->store);
    aux->var = v;
    aux->next = p;
    q_set(&aux->coeff, a);
    q->next = aux;
    b->nterms ++;
  }  
}


/*
 * Add monomial - a * v to b
 */
void arith_buffer_sub_mono(arith_buffer_t *b, arith_var_t v, rational_t *a) {
  mlist_t *p, *q, *aux;
  polynomial_manager_t *m;

  assert(polymanager_var_is_valid(&b->manager->pm, v));

  if (q_is_zero(a)) return;

  m = &b->manager->pm;
  p = b->list; // p == start marker (to be skipped)

  do {
    q = p; 
    p = q->next;
  } while (polymanager_var_precedes(m, p->var, v));

  if (p->var == v) {
    q_sub(&p->coeff, a);
  } else {
    aux = alloc_list_elem(b->store);
    aux->var = v;
    aux->next = p;
    q_set_neg(&aux->coeff, a);
    q->next = aux;
    b->nterms ++;
  }  
}


/*
 * Add 1 * v to b
 */
void arith_buffer_add_var(arith_buffer_t *b, arith_var_t v) {
  mlist_t *p, *q, *aux;
  polynomial_manager_t *m;

  assert(polymanager_var_is_valid(&b->manager->pm, v));

  m = &b->manager->pm;
  p = b->list; // p == start marker (to be skipped)

  do {
    q = p; 
    p = q->next;
  } while (polymanager_var_precedes(m, p->var, v));

  if (p->var == v) {
    q_add_one(&p->coeff);
  } else {
    aux = alloc_list_elem(b->store);
    aux->var = v;
    aux->next = p;
    q_set_one(&aux->coeff);
    q->next = aux;
    b->nterms ++;
  }  
}


/*
 * Add -1 * v to b
 */
void arith_buffer_sub_var(arith_buffer_t *b, arith_var_t v) {
  mlist_t *p, *q, *aux;
  polynomial_manager_t *m;

  assert(polymanager_var_is_valid(&b->manager->pm, v));

  m = &b->manager->pm;
  p = b->list; // p == start marker (to be skipped)

  do {
    q = p; 
    p = q->next;
  } while (polymanager_var_precedes(m, p->var, v));

  if (p->var == v) {
    q_sub_one(&p->coeff);
  } else {
    aux = alloc_list_elem(b->store);
    aux->var = v;
    aux->next = p;
    q_set_minus_one(&aux->coeff);
    q->next = aux;
    b->nterms ++;
  }  
}


/*
 * Add a constant c to b
 */
void arith_buffer_add_const(arith_buffer_t *b, rational_t *c) {
  arith_buffer_add_mono(b, const_idx, c);
}


/*
 * Subtract a constant c from b
 */
void arith_buffer_sub_const(arith_buffer_t *b, rational_t *c) {
  arith_buffer_sub_mono(b, const_idx, c);
}


/*
 * Add p1 to b. p1 must be normalized and terminated by max_idx
 */
void arith_buffer_add_monarray(arith_buffer_t *b, monomial_t *p1) {
  mlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  arith_var_t v;

  m = &b->manager->pm;
  p = b->list;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      q_add(&p->coeff, &p1->coeff);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 ++;
    v = p1->var;
  }
  
}


/*
 * Subtract p1 from b. p1 must be normalized and terminated by max_idx
 */
void arith_buffer_sub_monarray(arith_buffer_t *b, monomial_t *p1) {
  mlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  arith_var_t v;

  m = &b->manager->pm;
  p = b->list;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      q_sub(&p->coeff, &p1->coeff);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 ++;
    v = p1->var;
  }
  
}


/*
 * Add p1 * v1 to b. p1 must be normalized and terminated by max_idx.
 * v1 must be a valid variable.
 *
 * Works if v1 == const_idx (but much slower than arith_buffer_add).
 */
void arith_buffer_add_var_times_monarray(arith_buffer_t *b, monomial_t *p1, arith_var_t v1) {
  mlist_t *p, *q, *aux;
  arithvar_manager_t *m;
  polynomial_manager_t *pm;
  arith_var_t v;

  assert(polymanager_var_is_valid(&b->manager->pm, v1));

  m = b->manager;
  pm = &m->pm;
  p = b->list;
  v = p1->var;

  while (v < max_idx) {
    v = arithvar_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      q_add(&p->coeff, &p1->coeff);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 ++;
    v = p1->var;
  }
  
}


/*
 * Subtract p1 * v1 from b. p1 must be normalized and terminated by max_idx.
 */
void arith_buffer_sub_var_times_monarray(arith_buffer_t *b, monomial_t *p1, arith_var_t v1) {
  mlist_t *p, *q, *aux;
  arithvar_manager_t *m;
  polynomial_manager_t *pm;
  arith_var_t v;

  assert(polymanager_var_is_valid(&b->manager->pm, v1));

  m = b->manager;
  pm = &m->pm;
  p = b->list;
  v = p1->var;

  while (v < max_idx) {
    v = arithvar_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      q_sub(&p->coeff, &p1->coeff);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 ++;
    v = p1->var;
  }
  
}


/*
 * Add a * p1 to b. p1 must be normalized and terminated by max_idx.
 * a must be nonzero
 */
void arith_buffer_add_const_times_monarray(arith_buffer_t *b, monomial_t *p1, rational_t *a) {
  mlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  arith_var_t v;

  assert(q_is_nonzero(a));

  m = &b->manager->pm;
  p = b->list;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      q_addmul(&p->coeff, &p1->coeff, a);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff);
      q_mul(&aux->coeff, a);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 ++;
    v = p1->var;
  }
  
}

/*
 * Subtract a * p1 from b. p1 must be normalized and terminated by max_idx.
 * a must be nonzero
 */
void arith_buffer_sub_const_times_monarray(arith_buffer_t *b, monomial_t *p1, rational_t *a) {
  mlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  arith_var_t v;

  assert(q_is_nonzero(a));

  m = &b->manager->pm;
  p = b->list;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      q_submul(&p->coeff, &p1->coeff, a);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff);
      q_mul(&aux->coeff, a);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 ++;
    v = p1->var;
  }
  
}

/*
 * Add a * p1 * v1 to b. p1 must be normalized and terminated by max_idx
 * - a must be non-zero.
 */
void arith_buffer_add_mono_times_monarray(arith_buffer_t *b, monomial_t *p1, arith_var_t v1, rational_t *a) {
  mlist_t *p, *q, *aux;
  arithvar_manager_t *m;
  polynomial_manager_t *pm;
  arith_var_t v;

  assert(q_is_nonzero(a));
  assert(polymanager_var_is_valid(&b->manager->pm, v1));

  m = b->manager;
  pm = &m->pm;
  p = b->list;
  v = p1->var;

  while (v < max_idx) {
    v = arithvar_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      q_addmul(&p->coeff, &p1->coeff, a);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff);
      q_mul(&aux->coeff, a);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 ++;
    v = p1->var;
  }
  
}


/*
 * Subtract a * p1 * v1 from b. p1 must be normalized and terminated by max_idx.
 */
void arith_buffer_sub_mono_times_monarray(arith_buffer_t *b, monomial_t *p1, arith_var_t v1, rational_t *a) {
  mlist_t *p, *q, *aux;
  arithvar_manager_t *m;
  polynomial_manager_t *pm;
  arith_var_t v;

  assert(q_is_nonzero(a));
  assert(polymanager_var_is_valid(&b->manager->pm, v1));

  m = b->manager;
  pm = &m->pm;
  p = b->list;
  v = p1->var;

  while (v < max_idx) {
    v = arithvar_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      q_submul(&p->coeff, &p1->coeff, a);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff);
      q_mul(&aux->coeff, a);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 ++;
    v = p1->var;
  }

}


/*
 * Multiply b by p1.
 */
void arith_buffer_mul_monarray(arith_buffer_t *b, monomial_t *p1) {
  mlist_t *p, *q, *start;
  arith_var_t v;

  // reset b but keep list of monomials in p
  b->nterms = 0;
  start = b->list;
  p = start->next;

  // new end marker
  q = alloc_list_elem(b->store);
  q->next = NULL;
  q->var = max_idx;
  start->next = q;  

  q = p;
  v = p->var;

  if (v == const_idx) {
    arith_buffer_add_const_times_monarray(b, p1, &p->coeff);
    p = p->next;
    v = p->var;
  }

  while (v < max_idx) {
    arith_buffer_add_mono_times_monarray(b, p1, v, &p->coeff);
    p = p->next;
    v = p->var;
  }

  // free list q
  while (q->var < max_idx) {
    p = q->next;
    q_clear(&q->coeff);
    free_list_elem(b->store, q);
    q = p;
  }

  // don't call q_clear for end marker
  free_list_elem(b->store, q);
  
}

/*
 * Add p1 * p2 to b. p1 and p2 must be normalized and terminated by max_idx.
 */
void arith_buffer_add_monarray_times_monarray(arith_buffer_t *b, monomial_t *p1, monomial_t *p2) {
  arith_var_t v1;

  v1 = p1->var;

  // if p1 has a constant term, const_idx is first in p1
  if (v1 == const_idx) {
    arith_buffer_add_const_times_monarray(b, p2, &p1->coeff);
    p1 ++;
    v1 = p1->var;
  }

  while (v1 < max_idx) {
    arith_buffer_add_mono_times_monarray(b, p2, v1, &p1->coeff);
    p1++;
    v1 = p1->var;
  }
}


/*
 * Subtract p1 * p2 from b. p1 and p2 must be normalized and terminated by max_idx.
 */
void arith_buffer_sub_monarray_times_monarray(arith_buffer_t *b, monomial_t *p1, monomial_t *p2) {
  arith_var_t v1;

  v1 = p1->var;

  // if p1 has a constant term, const_idx is first in p1
  if (v1 == const_idx) {
    arith_buffer_sub_const_times_monarray(b, p2, &p1->coeff);
    p1 ++;
    v1 = p1->var;
  }

  while (v1 < max_idx) {
    arith_buffer_sub_mono_times_monarray(b, p2, v1, &p1->coeff);
    p1++;
    v1 = p1->var;
  }
}



/*
 * Add b1 to b. 
 * Should work when b == b1, but multiplying b by 2 should be faster.
 */
void arith_buffer_add_buffer(arith_buffer_t *b, arith_buffer_t *b1) {
  mlist_t *p, *p1, *q, *aux;
  polynomial_manager_t *m;
  arith_var_t v;

  m = &b->manager->pm;
  p = b->list;
  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      q_add(&p->coeff, &p1->coeff);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 = p1->next;
    v = p1->var;
  }
  
}


/*
 * Subtract b1 from b.
 * Should work with b == b1, but clear b is faster and gives a normalized result.
 */
void arith_buffer_sub_buffer(arith_buffer_t *b, arith_buffer_t *b1) {
  mlist_t *p, *p1, *q, *aux;
  polynomial_manager_t *m;
  arith_var_t v;

  m = &b->manager->pm;
  p = b->list;
  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      q_sub(&p->coeff, &p1->coeff);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 = p1->next;
    v = p1->var;
  }
  
}


/*
 * Add b1 * v1 to b.
 * Works if v1 == const_idx (but much slower than arith_buffer_add)
 * Should also work if b == b1.
 */
void arith_buffer_add_var_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_var_t v1) {
  mlist_t *p, *p1, *q, *aux;
  arithvar_manager_t *m;
  polynomial_manager_t *pm;
  arith_var_t v;

  assert(polymanager_var_is_valid(&b->manager->pm, v1));

  m = b->manager;
  pm = &m->pm;
  p = b->list;
  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    v = arithvar_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      q_add(&p->coeff, &p1->coeff);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 = p1->next;
    v = p1->var;
  }
  
}


/*
 * Subtract b1 * v1 from b.
 */
void arith_buffer_sub_var_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_var_t v1) {
  mlist_t *p, *p1, *q, *aux;
  arithvar_manager_t *m;
  polynomial_manager_t *pm;
  arith_var_t v;

  assert(polymanager_var_is_valid(&b->manager->pm, v1));

  m = b->manager;
  pm = &m->pm;
  p = b->list;
  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    v = arithvar_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      q_sub(&p->coeff, &p1->coeff);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 = p1->next;
    v = p1->var;
  }
  
}


/*
 * Add a * b1 to b. a must be nonzero
 */
void arith_buffer_add_const_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a) {
  mlist_t *p, *p1, *q, *aux;
  polynomial_manager_t *m;
  arith_var_t v;

  assert(q_is_nonzero(a));

  m = &b->manager->pm;
  p = b->list;
  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      q_addmul(&p->coeff, &p1->coeff, a);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff);
      q_mul(&aux->coeff, a);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 = p1->next;
    v = p1->var;
  }
  
}

/*
 * Subtract a * b1 from b.
 */
void arith_buffer_sub_const_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a) {
  mlist_t *p, *p1, *q, *aux;
  polynomial_manager_t *m;
  arith_var_t v;

  assert(q_is_nonzero(a));

  m = &b->manager->pm;
  p = b->list;
  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      q_submul(&p->coeff, &p1->coeff, a);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff);
      q_mul(&aux->coeff, a);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 = p1->next;
    v = p1->var;
  }
  
}

/*
 * Add a * v1 * b1 to b. a must be non-zero.
 */
void arith_buffer_add_mono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_var_t v1, rational_t *a) {
  mlist_t *p, *p1, *q, *aux;
  arithvar_manager_t *m;
  polynomial_manager_t *pm;
  arith_var_t v;

  assert(q_is_nonzero(a));
  assert(polymanager_var_is_valid(&b->manager->pm, v1));

  m = b->manager;
  pm = &m->pm;
  p = b->list;
  p1 =  b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    v = arithvar_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      q_addmul(&p->coeff, &p1->coeff, a);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff);
      q_mul(&aux->coeff, a);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 = p1->next;
    v = p1->var;
  }
  
}


/*
 * Subtract a * v1 * b1 from b.
 */
void arith_buffer_sub_mono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_var_t v1, rational_t *a) {
  mlist_t *p, *p1, *q, *aux;
  arithvar_manager_t *m;
  polynomial_manager_t *pm;
  arith_var_t v;

  assert(q_is_nonzero(a));
  assert(polymanager_var_is_valid(&b->manager->pm, v1));

  m = b->manager;
  pm = &m->pm;
  p = b->list;
  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    v = arithvar_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      q_submul(&p->coeff, &p1->coeff, a);
    } else {
      aux = alloc_list_elem(b->store);
      aux->var = v;
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff);
      q_mul(&aux->coeff, a);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }
    
    p1 = p1->next;
    v = p1->var;
  }

}


/*
 * Multiply b by b1. b must be distinct from b1.
 */
void arith_buffer_mul_buffer(arith_buffer_t *b, arith_buffer_t *b1) {
  mlist_t *p, *q, *start;
  arith_var_t v;

  assert(b != b1);

  // reset b but keep list of monomials in p
  b->nterms = 0;
  start = b->list;
  p = start->next;

  // new end marker
  q = alloc_list_elem(b->store);
  q->next = NULL;
  q->var = max_idx;
  start->next = q;
  
  q = p;
  v = p->var;

  if (v == const_idx) {
    arith_buffer_add_const_times_buffer(b, b1, &p->coeff);
    p = p->next;
    v = p->var;
  }

  while (v < max_idx) {
    arith_buffer_add_mono_times_buffer(b, b1, v, &p->coeff);
    p = p->next;
    v = p->var;
  }

  // free list q
  while (q->var < max_idx) {
    p = q->next;
    q_clear(&q->coeff);
    free_list_elem(b->store, q);
    q = p;
  }

  // don't call q_clear for end marker
  free_list_elem(b->store, q);  
}


/*
 * Compute the square of b
 */
void arith_buffer_square(arith_buffer_t *b) {
  arith_buffer_t aux;
  mlist_t *start;

  /*
   * Hackish: we make a shallow copy of b into aux then call mul
   * - for this to work, we must ensure aux->start
   *   is not the same as b->start
   */
  aux = *b;

  start = alloc_list_elem(aux.store);
  start->var = null_idx;
  start->next = aux.list->next;
  aux.list = start;

  arith_buffer_mul_buffer(b, &aux);

  /*
   * cleanup: all elements of aux have been freed by mul
   * except the start of the list.
   */
  free_list_elem(aux.store, start);
}


/*
 * Add b1 * b2 to b.
 */
void arith_buffer_add_buffer_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_buffer_t *b2) {
  mlist_t *p1;
  arith_var_t v1;

  assert(b != b1 && b != b2);  

  p1 = b1->list->next;
  v1 = p1->var;

  // if p1 has a constant term, const_idx is first in p1
  if (v1 == const_idx) {
    arith_buffer_add_const_times_buffer(b, b2, &p1->coeff);
    p1 = p1->next;
    v1 = p1->var;
  }

  while (v1 < max_idx) {
    arith_buffer_add_mono_times_buffer(b, b2, v1, &p1->coeff);
    p1 = p1->next;
    v1 = p1->var;
  }
}


/*
 * Subtract b1 * b2 from b.
 */
void arith_buffer_sub_buffer_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_buffer_t *b2) {
  mlist_t *p1;
  arith_var_t v1;

  assert(b != b1 && b != b2);  

  p1 = b1->list->next;
  v1 = p1->var;

  // if p1 has a constant term, const_idx is first in p1
  if (v1 == const_idx) {
    arith_buffer_sub_const_times_buffer(b, b2, &p1->coeff);
    p1 = p1->next;
    v1 = p1->var;
  }

  while (v1 < max_idx) {
    arith_buffer_sub_mono_times_buffer(b, b2, v1, &p1->coeff);
    p1 = p1->next;
    v1 = p1->var;
  }
}



/*
 * Comparison with a monarray
 * - b and p1 must be normalized.
 */
bool arith_buffer_equal_monarray(arith_buffer_t *b, monomial_t *p1) {
  mlist_t *p;
  arith_var_t v, v1;

  p = b->list->next;
  v = p->var;
  v1 = p1->var;

  while (v == v1) {
    if (v == max_idx) return true;
    if (q_neq(&p->coeff, &p1->coeff)) return false;

    p = p->next;
    v = p->var;
    p1 ++;
    v1 = p1->var;
  }

  return false;
}


/*
 * Comparison with a buffer b1
 * - b and b1 must be normalized.
 */
bool arith_buffer_equal_buffer(arith_buffer_t *b, arith_buffer_t *b1) {
  mlist_t *p, *p1;
  arith_var_t v, v1;

  if (b->nterms != b1->nterms) return false;

  p = b->list->next;
  v = p->var;
  p1 = b1->list->next;
  v1 = p1->var;

  while (v == v1) {
    if (v == max_idx) return true;
    if (q_neq(&p->coeff, &p1->coeff)) return false;

    p = p->next;
    v = p->var;
    p1 = p1->next;
    v1 = p1->var;
  }

  return false;
}



