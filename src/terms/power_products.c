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
 * Products of variables: x_1^d_1 ... x_n^d_n
 *
 * These are used to represent polynomials
 * Variables are just integer indices
 */

#include <assert.h>
#include <stdbool.h>

#include "terms/power_products.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"
#include "utils/prng.h"

#include "yices_limits.h"


/*
 * Initialization and deletion of buffers
 */
void init_pp_buffer(pp_buffer_t *b, uint32_t n) {
  if (n >= PPROD_MAX_LENGTH) {
    out_of_memory();
  }
  b->size = n;
  b->len = 0;
  b->prod = (varexp_t *) safe_malloc(n * sizeof(varexp_t));
}

void delete_pp_buffer(pp_buffer_t *b) {
  safe_free(b->prod);
  b->prod = NULL;
}


/*
 * Auxiliary functions
 */
// make buffer 50% larger
static void pp_buffer_extend(pp_buffer_t *b) {
  uint32_t n;

  n = b->size + 1;
  n += n >> 1;
  if (n >= PPROD_MAX_LENGTH) {
    out_of_memory();
  }
  b->prod = (varexp_t *) safe_realloc(b->prod, n * sizeof(varexp_t));
  b->size = n;
}

// make it large enough for at least n elements
static void pp_buffer_resize(pp_buffer_t *b, uint32_t n) {
  uint32_t new_size;

  if (b->size < n) {
    new_size = b->size + 1;
    new_size += new_size >> 1;
    if (new_size < n) new_size = n;

    if (new_size >= PPROD_MAX_LENGTH) {
      out_of_memory();
    }
    b->prod = (varexp_t *) safe_realloc(b->prod, new_size * sizeof(varexp_t));
    b->size = new_size;
  }
}

// add pair v^d to the buffer
static void pp_buffer_pushback(pp_buffer_t *b, int32_t v, uint32_t d) {
  uint32_t i;

  i = b->len;
  if (i == b->size) {
    pp_buffer_extend(b);
  }
  assert(i < b->size);
  b->prod[i].var = v;
  b->prod[i].exp = d;
  b->len = i + 1;
}

// add pairs v[0]^d[0] ... v[n-1]^d[n-1]
static void pp_buffer_pusharray(pp_buffer_t *b, uint32_t n, int32_t *v, uint32_t *d) {
  uint32_t i, l;

  l = b->len;
  pp_buffer_resize(b, l + n);
  for (i=0; i<n; i++) {
    b->prod[l+i].var = v[i];
    b->prod[l+i].exp = d[i];
  }
  b->len = l + n;
}

// add pairs v[0]^1 ... v[n-1]^1
static void pp_buffer_pushvars(pp_buffer_t *b, uint32_t n, int32_t *v) {
  uint32_t i, l;

  l = b->len;
  pp_buffer_resize(b, l + n);
  for (i=0; i<n; i++) {
    b->prod[l+i].var = v[i];
    b->prod[l+i].exp = 1;
  }
  b->len = l + n;
}

// variant: pairs are in varexp array a
static void pp_buffer_push_varexp_array(pp_buffer_t *b, uint32_t n, varexp_t *a) {
  uint32_t i, l;

  l = b->len;
  pp_buffer_resize(b, l + n);
  for (i=0; i<n; i++) {
    b->prod[l + i] = a[i];
  }
  b->len = l + n;
}



/*
 * NORMALIZATION
 */

/*
 * Sort in increasing order of variables:
 * - a = array of pairs <variable, exponent>
 * - n = size of the array.
 */
static void isort_varexp_array(varexp_t *a, uint32_t n);
static void qsort_varexp_array(varexp_t *a, uint32_t n);

static inline void sort_varexp_array(varexp_t *a, uint32_t n) {
  if (n <= 10) {
    isort_varexp_array(a, n);
  } else {
    qsort_varexp_array(a, n);
  }
}

static void isort_varexp_array(varexp_t *a, uint32_t n) {
  uint32_t i, j, d, e;
  int32_t v, w;

  for (i=1; i<n; i++) {
    v = a[i].var;
    d = a[i].exp;
    j = 0;
    while (a[j].var < v) j ++;
    while (j < i) {
      w = a[j].var; a[j].var = v; v = w;
      e = a[j].exp; a[j].exp = d; d = e;
      j ++;
    }
    a[j].var = v;
    a[j].exp = d;
  }
}

static void qsort_varexp_array(varexp_t *a, uint32_t n) {
  uint32_t i, j;
  int32_t pivot;
  varexp_t aux;
  uint32_t seed = PRNG_DEFAULT_SEED;

  // random pivot
  i = random_uint(&seed, n);
  aux = a[i];
  pivot = a[i].var;

  // swap with a[0];
  a[i] = a[0];
  a[0] = aux;

  i = 0;
  j = n;

  // The test i <= j in the second loop is required for termination
  // if all elements are smaller than the pivot.
  do { j--; } while (a[j].var > pivot);
  do { i++; } while (i <= j && a[i].var < pivot);

  while (i < j) {
    aux = a[i]; a[i] = a[j]; a[j] = aux;

    do { j--; } while (a[j].var > pivot);
    do { i++; } while (a[i].var < pivot);
  }

  // swap pivot = a[0] and a[j]
  aux = a[0]; a[0] = a[j]; a[j] = aux;

  // sort a[0 ... j-1] and a[j+1 ... n-1]
  sort_varexp_array(a, j);
  j ++;
  sort_varexp_array(a + j, n - j);
}



/*
 * Sort then merge pairs <var, d> with the same var.
 * Also remove pairs <var, d> with d = 0.
 * return the number of elements remaining after normalization
 */
static uint32_t normalize_varexp_array(varexp_t *a, uint32_t n) {
  uint32_t i, j, d;
  int32_t v;

  if (n == 0) return n;

  sort_varexp_array(a, n);

  j = 0;
  d = a[0].exp;
  v = a[0].var;
  for (i=1; i<n; i++) {
    if (a[i].var == v) {
      d += a[i].exp;
    } else {
      if (d != 0) {
        a[j].var = v;
        a[j].exp = d;
        j ++;
      }
      v = a[i].var;
      d = a[i].exp;
    }
  }

  if (d != 0) {
    a[j].var = v;
    a[j].exp = d;
    j ++;
  }

  return j;
}


void pp_buffer_normalize(pp_buffer_t *b) {
  b->len = normalize_varexp_array(b->prod, b->len);
}


/*
 * API: exported operations
 */
void pp_buffer_reset(pp_buffer_t *b) {
  b->len = 0;
}

void pp_buffer_set_var(pp_buffer_t *b, int32_t v) {
  b->len = 0;
  pp_buffer_pushback(b, v, 1);
}

void pp_buffer_set_varexp(pp_buffer_t *b, int32_t v, uint32_t d) {
  b->len = 0;
  pp_buffer_pushback(b, v, d);
}

void pp_buffer_set_vars(pp_buffer_t *b, uint32_t n, int32_t *v) {
  b->len = 0;
  pp_buffer_pushvars(b, n, v);
}

void pp_buffer_set_varexps(pp_buffer_t *b, uint32_t n, int32_t *v, uint32_t *d) {
  b->len = 0;
  pp_buffer_pusharray(b, n, v, d);
}

void pp_buffer_set_pprod(pp_buffer_t *b, pprod_t *p) {
  assert(p != end_pp);

  b->len = 0;
  if (pp_is_var(p)) {
    pp_buffer_pushback(b, var_of_pp(p), 1);
  } else if (!pp_is_empty(p)) {
    pp_buffer_push_varexp_array(b, p->len, p->prod);
  }
}

void pp_buffer_copy(pp_buffer_t *b, pp_buffer_t *src) {
  b->len = 0;
  pp_buffer_push_varexp_array(b, src->len, src->prod);
}


void pp_buffer_mul_var(pp_buffer_t *b, int32_t v) {
  pp_buffer_pushback(b, v, 1);
  pp_buffer_normalize(b);
}

void pp_buffer_mul_varexp(pp_buffer_t *b, int32_t v, uint32_t d) {
  pp_buffer_pushback(b, v, d);
  pp_buffer_normalize(b);
}

void pp_buffer_mul_vars(pp_buffer_t *b, uint32_t n, int32_t *v) {
  pp_buffer_pushvars(b, n, v);
  pp_buffer_normalize(b);
}

void pp_buffer_mul_varexps(pp_buffer_t *b, uint32_t n, int32_t *v, uint32_t *d) {
  pp_buffer_pusharray(b, n, v, d);
  pp_buffer_normalize(b);
}

void pp_buffer_mul_pprod(pp_buffer_t *b, pprod_t *p) {
  assert(p != end_pp);

  if (pp_is_var(p)) {
    pp_buffer_pushback(b, var_of_pp(p), 1);
  } else if (! pp_is_empty(p)) {
    pp_buffer_push_varexp_array(b, p->len, p->prod);
  }
  pp_buffer_normalize(b);
}

void pp_buffer_mul_buffer(pp_buffer_t *b, pp_buffer_t *src) {
  pp_buffer_push_varexp_array(b, src->len, src->prod);
  pp_buffer_normalize(b);
}


void pp_buffer_push_var(pp_buffer_t *b, int32_t v) {
  pp_buffer_pushback(b, v, 1);
}

void pp_buffer_push_varexp(pp_buffer_t *b, int32_t v, uint32_t d) {
  pp_buffer_pushback(b, v, d);
}


/*
 * Exponentiation
 */
void pp_buffer_exponentiate(pp_buffer_t *b, uint32_t d) {
  uint32_t i, n;

  n = b->len;
  for (i=0; i<n; i++) {
    b->prod[i].exp *= d;
  }
  pp_buffer_normalize(b);
}


/*
 * Degree
 */
static uint32_t varexp_array_degree(varexp_t *a, int32_t n) {
  uint32_t d, i;

  d = 0;
  for (i=0; i<n; i++) {
    d += a[i].exp;
  }
  return d;
}

uint32_t pp_buffer_degree(pp_buffer_t *b) {
  return varexp_array_degree(b->prod, b->len);
}

uint32_t pprod_degree(pprod_t *p) {
  uint32_t d;

  assert(p != end_pp);

  d = 0;
  if (pp_is_var(p)) {
    d = 1;
  } else if (! pp_is_empty(p)) {
    d = p->degree;
  }
  return d;
}


/*
 * Check that degree is less than YICES_MAX_DEGREE
 */
static bool below_max_degree(varexp_t *a, uint32_t n) {
  uint32_t d, i, e;

  d = 0;
  for (i=0; i<n; i++) {
    e = a[i].exp;
    if (e >= YICES_MAX_DEGREE) return false;
    d += e;
    if (d >= YICES_MAX_DEGREE) return false;
  }

  return true;
}

bool pp_buffer_below_max_degree(pp_buffer_t *b) {
  return below_max_degree(b->prod, b->len);
}

bool pprod_below_max_degree(pprod_t *p) {
  return pprod_degree(p) < YICES_MAX_DEGREE;
}



/*
 * Degree of a variable x in a product p
 * - we use a sequential search since n is usually small
 */
static uint32_t varexp_array_var_degree(varexp_t *a, uint32_t n, int32_t x) {
  uint32_t d, i;

  d = 0;
  for (i=0; i<n; i++) {
    if (a[i].var == x) {
      d = a[i].exp;
      break;
    }
  }
  return d;
}

uint32_t pp_buffer_var_degree(pp_buffer_t *b, int32_t x) {
  return varexp_array_var_degree(b->prod, b->len, x);
}

uint32_t pprod_var_degree(pprod_t *p, int32_t x) {
  uint32_t d;

  assert(p != end_pp);

  d = 0;
  if (pp_is_var(p)) {
    d = (var_of_pp(p) == x);
  } else if (! pp_is_empty(p)) {
    d =varexp_array_var_degree(p->prod, p->len, x);
  }
  return d;
}



/*
 * Build a pprod object by making a copy of a
 * - a must be normalized
 * - n = length of a
 * - n must be less than PPROD_MAX_LENGTH
 */
pprod_t *make_pprod(varexp_t *a, uint32_t n) {
  pprod_t *p;
  uint32_t i;

  assert(0 <= n && n < PPROD_MAX_LENGTH);

  if (n == 0) {
    p = empty_pp;
  } else if (n == 1 && a[0].exp == 1) {
    p = var_pp(a[0].var);
  } else {
    p = (pprod_t *) safe_malloc(sizeof(pprod_t) + n * sizeof(varexp_t));
    p->len = n;
    p->degree = varexp_array_degree(a, n);
    for (i=0; i<n; i++) {
      p->prod[i] = a[i];
    }
  }

  return p;
}


/*
 * Construct a pprod object from buffer b
 */
pprod_t *pp_buffer_getprod(pp_buffer_t *b) {
  return make_pprod(b->prod, b->len);
}



/*
 * Free the object constructed by make_pprod
 */
void free_pprod(pprod_t *p) {
  if (! pp_is_var(p) && ! pp_is_empty(p)) {
    safe_free(p);
  }
}


/*
 * Comparison: two arrays of the same length n
 * Both arrays must be normalized.
 */
bool varexp_array_equal(varexp_t *a, varexp_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i].var != b[i].var || a[i].exp != b[i].exp) {
      return false;
    }
  }
  return true;
}


/*
 * Check whether b1 and b2 are equal
 * - both must be normalized
 */
bool pp_buffer_equal(pp_buffer_t *b1, pp_buffer_t *b2) {
  return b1->len == b2->len && varexp_array_equal(b1->prod, b2->prod, b1->len);
}


/*
 * Minimum of two exponent
 */
static inline uint32_t min_exp(uint32_t e1, uint32_t e2) {
  return (e1 < e2) ? e1 : e2;
}

/*
 * Compute the common factors of b and b1. Store the result in b.
 * - b and b1 must be normalized
 * - the result is normalized (on exit)
 */
void pp_buffer_gcd(pp_buffer_t *b, pp_buffer_t *b1) {
  uint32_t i, j, n, d;
  int32_t x;

  n = b->len;
  j = 0;
  for (i=0; i<n; i++) {
    assert(b->prod[i].exp > 0);
    x = b->prod[i].var;
    d = pp_buffer_var_degree(b1, x);
    if (d == 0) continue; // remove x
    b->prod[j].var = x;
    b->prod[j].exp = min_exp(d, b->prod[i].exp);
    j ++;
  }
  b->len = j;
}


/*
 * Divide b by b1. Store the result in b
 * - b and b1 must be normalized.
 *
 * The actual operation is more general:
 * We replace x^e in b  by  x^max(0, e - d) where d = exponent of x in b1.
 * So x disappears if e <= d, and x has exponent (e - d) in the result otherwise.
 */
void pp_buffer_divide(pp_buffer_t *b, pp_buffer_t *b1) {
  uint32_t i, j, n, d;
  int32_t x;

  n = b->len;
  j = 0;
  for (i=0; i<n; i++) {
    assert(b->prod[i].exp > 0);
    x = b->prod[i].var;
    d = pp_buffer_var_degree(b1, x);
    if (d >= b->prod[i].exp) continue;
    b->prod[j].var = x;
    b->prod[j].exp = b->prod[i].exp - d;
    j ++;
  }
  b->len = j;
}


/*
 * Divide p by variable x
 */
void pp_buffer_divide_by_var(pp_buffer_t *b, int32_t x) {
  uint32_t i, n;

  n = b->len;
  for (i=0; i<n; i++) {
    assert(b->prod[i].exp > 0);
    if (b->prod[i].var == x) goto found;
  }

  return; // x does not occur in b.

 found:
  assert(i < n && b->prod[i].var == x && b->prod[i].exp > 0);
  b->prod[i].exp --;
  if (b->prod[i].exp == 0) {
    i ++;
    while (i < n) {
      b->prod[i-1] = b->prod[i];
      i ++;
    }
    b->len = n-1;
  }
}


/*
 * The ordering between power products must be compatible with the
 * product and with the ordering on variables. That is, we want
 *  1) a < b => a * c < b * c for any c
 *  2) x < y as variables => x^1 y^0 < x^0 y^1
 *
 * The lexical ordering defined as follows works:
 * Let a = x_1^d_1 .... x_n^d_n and b = x_1^c_1 ... x_n^c_n
 * then a < b if for some i we have
 *   d_1 = c_1 and ...  and d_{i-1} = c_{i-1} and d_i > c_i
 *
 * Input:
 * - a and b must be normalized, na = length of a, nb = length of b
 * Output:
 * - a negative number if a < b
 * - zero if a == b
 * - a positive number if a > b
 */
static int32_t varexp_array_lexcmp(varexp_t *a, uint32_t na, varexp_t *b, uint32_t nb) {
  uint32_t i, n;
  int32_t x;

  n = (na < nb) ? na : nb;

  i = 0;
  while (i<n && a[i].var == b[i].var && a[i].exp == b[i].exp) {
    i++;
  }

  if (i < n) {
    /*
     * let x_b = b[i].var and x_a = a[i].var
     *     d_b = b[i].exp and d_a = a[i].exp
     *
     * cases:
     *  x_a == x_b and d_a < d_b --> b smaller than a
     *  x_a == x_b and d_a > d_b --> a smaller than b
     *  x_a < x_b --> a smaller than b
     *  x_a > x_b --> b smaller than a
     */
    x = a[i].var - b[i].var;
    if (x == 0) {
      // the conversion to int32_t is safe if the total
      // degree of a and b is less than YICES_MAX_DEGREE
      assert(((int32_t) b[i].exp >= 0) && ((int32_t) a[i].exp >= 0));
      return (int32_t) (b[i].exp - a[i].exp);
    } else {
      return x;
    }
  } else {
    /*
     * if na < nb, a is a prefix of b so a < b
     * if nb < na, b is a prefix of a so b < a
     */
    return na - nb;
  }
}


/*
 * Lexicographic comparison: p1 and p2 must be normalized
 */
int32_t pprod_lex_cmp(pprod_t *p1, pprod_t *p2) {
  varexp_t aux1, aux2;
  varexp_t *a, *b;
  uint32_t na, nb;

  assert(p1 != end_pp && p2 != end_pp);

  na = 0;
  a = NULL;
  if (pp_is_var(p1)) {
    aux1.var = var_of_pp(p1);
    aux1.exp = 1;
    a = &aux1;
    na = 1;
  } else if (! pp_is_empty(p1)) {
    a = p1->prod;
    na = p1->len;
  }

  nb = 0;
  b = NULL;
  if (pp_is_var(p2)) {
    aux2.var = var_of_pp(p2);
    aux2.exp = 1;
    b = &aux2;
    nb = 1;
  } else if (! pp_is_empty(p2)) {
    b = p2->prod;
    nb = p2->len;
  }

  return varexp_array_lexcmp(a, na, b, nb);
}



/*
 * Check whether p1 precedes p2 (strictly) in the degree + lex ordering
 */
bool pprod_precedes(pprod_t *p1, pprod_t *p2) {
  uint32_t d1, d2;

  if (p1 == p2) return false;
  if (p1 == end_pp) return false;
  if (p2 == end_pp) return true;

  d1 = pprod_degree(p1);
  d2 = pprod_degree(p2);
  return (d1 < d2) || (d1 == d2 && pprod_lex_cmp(p1, p2) < 0);
}


/*
 * Test whether a divides b
 */
static bool varexp_array_divides(varexp_t *a, uint32_t na, varexp_t *b, uint32_t nb) {
  uint32_t i, j;
  int32_t v;

  if (na > nb) return false;

  j = 0;
  for (i=0; i<na; i++) {
    v = a[i].var;
    while (j < nb && b[j].var < v) {
      j++;
    }
    if (j == nb || b[j].var > v || a[i].exp > b[j].exp) {
      return false;
    }
  }

  return true;
}


/*
 * Test whether p1 divides p2
 */
bool pprod_divides(pprod_t *p1, pprod_t *p2) {
  varexp_t aux1, aux2;
  varexp_t *a, *b;
  uint32_t na, nb;

  assert(p1 != end_pp && p2 != end_pp);

  na = 0;
  a = NULL;
  if (pp_is_var(p1)) {
    aux1.var = var_of_pp(p1);
    aux1.exp = 1;
    a = &aux1;
    na = 1;
  } else if (! pp_is_empty(p1)) {
    a = p1->prod;
    na = p1->len;
  }

  nb = 0;
  b = NULL;
  if (pp_is_var(p2)) {
    aux2.var = var_of_pp(p2);
    aux2.exp = 1;
    b = &aux2;
    nb = 1;
  } else if (! pp_is_empty(p2)) {
    b = p2->prod;
    nb = p2->len;
  }

  return varexp_array_divides(a, na, b, nb);
}




/*
 * Check whether p1 divides p2 and if so store (p2/p1) in b
 */
bool pprod_divisor(pp_buffer_t *b, pprod_t *p1, pprod_t *p2) {
  uint32_t i, j, n;
  int32_t v;
  varexp_t *a1, *a2;
  varexp_t aux;

  assert(p1 != end_pp && p2 != end_pp);

  if (pp_is_empty(p1)) {
    n = 0;
    a1 = NULL;
  } else if (pp_is_var(p1)) {
    aux.var = var_of_pp(p1);
    aux.exp = 1;
    n = 1;
    a1 = &aux;
  } else {
    n = p1->len;
    a1 = p1->prod;
  }

  pp_buffer_set_pprod(b, p2);
  if (n > b->len) return false;

  pp_buffer_pushback(b, INT32_MAX, UINT32_MAX); // add an end marker

  a2 = b->prod;

  j =0;
  for (i=0; i<n; i++) {
    v = a1[i].var;
    while (a2[j].var < v) j++;
    if (a2[j].var > v || a2[j].exp < a1[i].exp) return false;
    a2[j].exp -= a1[i].exp;
    j ++;
  }

  // normalization: remove zero exponents and end marker
  b->len --;
  i = 0;
  for (j=0; j<b->len; j++) {
    if (a2[j].exp > 0) {
      a2[i] = a2[j];
      i ++;
    }
  }

  b->len = i;

  return true;
}


/*
 * Check whether p1 and p2 are equal
 */
bool pprod_equal(pprod_t *p1, pprod_t *p2) {
  assert(p1 != end_pp && p2 != end_pp);

  if (p1 == p2) return true;

  if (pp_is_var(p1) || pp_is_var(p2)) {
    // p1 and p2 are distinct variables
    // or only one of them is a variable
    return false;
  }

  if (pp_is_empty(p1) || pp_is_empty(p2)) {
    // one empty and the other is not
    return false;
  }

  // two non-empty, non variable power products
  return p1->len == p2->len && varexp_array_equal(p1->prod, p2->prod, p1->len);
}

