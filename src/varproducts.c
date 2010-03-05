/*
 * Products of variables: x_1^d_1 ... x_n^d_n 
 *
 * These are used to represent polynomials
 * Variables are just integer indices
 */

#include <assert.h>
#include <stdbool.h>

#include "memalloc.h"
#include "varproducts.h"
#include "prng.h"


/*
 * Initialization and deletetion of buffers
 */
void init_vpbuffer(vpbuffer_t *b, int32_t n) {
  assert(n >= 0);

  if (n >= MAX_VARPROD_LENGTH) {
    out_of_memory();
  }
  b->size = n;
  b->len = 0;
  b->prod = (varexp_t *) safe_malloc(n * sizeof(varexp_t));
}

void delete_vpbuffer(vpbuffer_t *b) {
  safe_free(b->prod);
  b->prod = NULL;
}


/*
 * Auxiliary functions
 */
// make buffer 50% larger
static void vpbuffer_extend(vpbuffer_t *b) {
  int32_t n;

  n = b->size + 1;
  n += n >> 1;
  if (n >= MAX_VARPROD_LENGTH) {
    out_of_memory();
  }
  b->prod = (varexp_t *) safe_realloc(b->prod, n * sizeof(varexp_t));
  b->size = n;
}

// make it large enough for at least n elements
static void vpbuffer_resize(vpbuffer_t *b, int32_t n) {
  int32_t new_size;
  if (b->size < n) {
    new_size = b->size + 1;
    new_size += new_size >> 1;
    if (new_size < n) new_size = n;

    if (new_size >= MAX_VARPROD_LENGTH) {
      out_of_memory();
    }
    b->prod = (varexp_t *) safe_realloc(b->prod, new_size * sizeof(varexp_t));
    b->size = new_size;
  }
}

// add pair v^d to the buffer
static void vpbuffer_pushback(vpbuffer_t *b, int32_t v, int32_t d) {
  int32_t i;
  i = b->len;
  if (i == b->size) {
    vpbuffer_extend(b);
  }
  b->prod[i].var = v;
  b->prod[i].exp = d;
  b->len = i + 1;
}

// add pairs v[0]^d[0] ... v[n-1]^d[n-1]
static void vpbuffer_pusharray(vpbuffer_t *b, int32_t n, int32_t *v, int32_t *d) {
  int32_t i, l;
  l = b->len;
  vpbuffer_resize(b, l + n);
  for (i=0; i<n; i++) {
    b->prod[l+i].var = v[i];
    b->prod[l+i].exp = d[i];    
  }
  b->len = l + n;
}

// add pairs v[0]^1 ... v[n-1]^1
static void vpbuffer_pushvars(vpbuffer_t *b, int32_t n, int32_t *v) {
  int32_t i, l;
  l = b->len;
  vpbuffer_resize(b, l + n);

  for (i=0; i<n; i++) {
    b->prod[l+i].var = v[i];
    b->prod[l+i].exp = 1;
  }
  b->len = l + n;
}

// variant: pairs are in varexp array a
static void vpbuffer_push_varexp_array(vpbuffer_t *b, int32_t n, varexp_t *a) {
  int32_t i, l;
  l = b->len;
  vpbuffer_resize(b, l + n);
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
static void isort_varexp_array(varexp_t *a, int32_t n);
static void qsort_varexp_array(varexp_t *a, int32_t n);

static inline void sort_varexp_array(varexp_t *a, int32_t n) {
  if (n <= 10) {
    isort_varexp_array(a, n);
  } else {
    qsort_varexp_array(a, n);
  }
}

static void isort_varexp_array(varexp_t *a, int32_t n) {
  int32_t i, j;
  int32_t v, d, aux;

  for (i=1; i<n; i++) {
    v = a[i].var;
    d = a[i].exp;
    j = 0;
    while (a[j].var < v) j ++;
    while (j < i) {
      aux = a[j].var; a[j].var = v; v = aux;
      aux = a[j].exp; a[j].exp = d; d = aux;
      j ++;
    }
    a[j].var = v;
    a[j].exp = d;
  }
}

static void qsort_varexp_array(varexp_t *a, int32_t n) {
  int32_t i, j, pivot;
  varexp_t aux;

  // random pivot
  i = random_uint(n);
  aux = a[i];
  pivot = a[i].var;

  // swap with a[0];
  a[i] = a[0];
  a[0] = aux;

  i = 0;
  j = n;

  // test i <= j in second loop is required for termination
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
 * Merge pairs <var, d> with the same var.
 * Remove pairs <var, d> with d = 0.
 * return the number of elements remaining after normalization
 */
static int32_t normalize_varexp_array(varexp_t *a, int32_t n) {
  int32_t i, j, d, v;

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


void vpbuffer_normalize(vpbuffer_t *b) {
  b->len = normalize_varexp_array(b->prod, b->len);
}


/*
 * API: exported operations
 */
void vpbuffer_reset(vpbuffer_t *b) {
  b->len = 0;
}

void vpbuffer_set_var(vpbuffer_t *b, int32_t v) {
  b->len = 0;
  vpbuffer_pushback(b, v, 1);
}

void vpbuffer_set_varexp(vpbuffer_t *b, int32_t v, int32_t d) {
  b->len = 0;
  vpbuffer_pushback(b, v, d);
}

void vpbuffer_set_vars(vpbuffer_t *b, int32_t n, int32_t *v) {
  b->len = 0;
  vpbuffer_pushvars(b, n, v);
}

void vpbuffer_set_varexps(vpbuffer_t *b, int32_t n, int32_t *v, int32_t *d) {
  b->len = 0;
  vpbuffer_pusharray(b, n, v, d);
}

void vpbuffer_set_varprod(vpbuffer_t *b, varprod_t *p) {
  b->len = 0;
  vpbuffer_push_varexp_array(b, p->len, p->prod);
}

void vpbuffer_copy(vpbuffer_t *b, vpbuffer_t *src) {
  b->len = 0;
  vpbuffer_push_varexp_array(b, src->len, src->prod);
}


void vpbuffer_mul_var(vpbuffer_t *b, int32_t v) {
  vpbuffer_pushback(b, v, 1);
  vpbuffer_normalize(b);
}

void vpbuffer_mul_varexp(vpbuffer_t *b, int32_t v, int32_t d) {
  vpbuffer_pushback(b, v, d);
  vpbuffer_normalize(b);
}

void vpbuffer_mul_vars(vpbuffer_t *b, int32_t n, int32_t *v) {
  vpbuffer_pushvars(b, n, v);
  vpbuffer_normalize(b);
}

void vpbuffer_mul_varexps(vpbuffer_t *b, int32_t n, int32_t *v, int32_t *d) {
  vpbuffer_pusharray(b, n, v, d);
  vpbuffer_normalize(b);
}

void vpbuffer_mul_varprod(vpbuffer_t *b, varprod_t *p) {
  vpbuffer_push_varexp_array(b, p->len, p->prod);
  vpbuffer_normalize(b);
}

void vpbuffer_mul_buffer(vpbuffer_t *b, vpbuffer_t *src) {
  vpbuffer_push_varexp_array(b, src->len, src->prod);
  vpbuffer_normalize(b);
}



/*
 * Build a vaprod object by making a copy of a
 * - a must be normalized
 * - n = lentgh of a
 * - n must be less than MAX_VARPROD_LENGTH
 */
varprod_t *make_varprod(varexp_t *a, int32_t n) {
  varprod_t *p;
  int32_t i;

  assert(0 <= n && n < MAX_VARPROD_LENGTH);
  p = (varprod_t *) safe_malloc(sizeof(varprod_t) + n * sizeof(varexp_t));
  p->len = n;
  for (i=0; i<n; i++) {
    p->prod[i] = a[i];
  }
  return p;
}


/*
 * Construct a varprod object from buffer b
 */
varprod_t *vpbuffer_getprod(vpbuffer_t *b) {
  return make_varprod(b->prod, b->len);
}



/*
 * Degree
 */
static int32_t varexp_array_degree(varexp_t *a, int32_t n) {
  int32_t d, i;

  d = 0;
  for (i=0; i<n; i++) {
    d += a[i].exp;
  }
  return d;
}

int32_t vpbuffer_degree(vpbuffer_t *b) {
  return varexp_array_degree(b->prod, b->len);
}

int32_t varprod_degree(varprod_t *p) {
  return varexp_array_degree(p->prod, p->len);
}


/*
 * Check that degree is less than MAX_DEGREE
 */
static bool below_max_degree(varexp_t *a, int32_t n) {
  int32_t d, i, e;

  d = 0;
  for (i=0; i<n; i++) {
    e = a[i].exp;
    if (e >= MAX_DEGREE) return false;
    d += e;
    if (d >= MAX_DEGREE) return false;
  }

  return true;
}

bool vpbuffer_below_max_degree(vpbuffer_t *b) {
  return below_max_degree(b->prod, b->len);
}

bool varprod_below_max_degree(varprod_t *p) {
  return below_max_degree(p->prod, p->len);
}



/*
 * Degree of a variable x in a product p
 */
static int32_t varexp_array_var_degree(varexp_t *a, int32_t n, int32_t x) {
  int32_t d, i;

  d = 0;
  for (i=0; i<n; i++) {
    if (a[i].var == x) {
      d = a[i].exp;
      break;
    }
  }
  return d;
}

int32_t vpbuffer_var_degree(vpbuffer_t *b, int32_t x) {
  return varexp_array_var_degree(b->prod, b->len, x);
}

int32_t varprod_var_degree(varprod_t *p, int32_t x) {
  return varexp_array_var_degree(p->prod, p->len, x);
}





/*
 * Comparison: two arrays of the same length n
 * They must be normalized.
 */
bool varexp_array_equal(varexp_t *a, varexp_t *b, int32_t n) {
  int32_t i;

  for (i=0; i<n; i++) {
    if (a[i].var != b[i].var || a[i].exp != b[i].exp) {
      return false;
    }
  }
  return true;
}



/*
 * Ordering must be compatible with product and with the ordering on
 * primitive variables. We want 
 *  1) a < b => a * c < b * c for any c
 *  2) x < y as variables => x^1 y^0 < x^0 y^1 
 * 
 * Lexical ordering defined as follows works:
 * Let a = x_1^d_1 .... x_n^d_n and b = x_1^c_1 ... x_n^c_n
 * then a < b if for some i we have
 *   d_1 = c_1 and ...  and d_{i-1} = c_{i-1} and d_i > c_i
 * 
 * Input:
 * - a and b must be normalized, na = length of a, nb = length of b
 * Output:
 * - negative number if a < b
 * - zero if a == b
 * - positive number if a > b
 */
static int32_t varexp_array_lexcmp(varexp_t *a, int32_t na, varexp_t *b, int32_t nb) {
  int32_t i, n, x;

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
      return b[i].exp - a[i].exp;
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
 * test whether a divides b
 */
static bool varexp_array_divides(varexp_t *a, int32_t na, varexp_t *b, int32_t nb) {
  int32_t i, j, v;

  if (na > nb) return false;

  j = 0;
  for (i=0; i<na; i++) {
    v = a[i].var;
    while (j < nb && b[j].var < v) { 
      j++; 
    }
    if (j == nb || b[j].var > v || a[i].exp > b[j].exp) 
      return false;
  }

  return true;
}

/*
 * Exported functions
 */
int32_t varprod_lex_cmp(varprod_t *p1, varprod_t *p2) {
  return varexp_array_lexcmp(p1->prod, p1->len, p2->prod, p2->len);
}

/*
 * Check whether buffer b and product p are equal
 */
bool varprod_equal(varprod_t *p1, varprod_t *p2) {
  return p1->len == p2->len && varexp_array_equal(p1->prod, p2->prod, p1->len);
}

bool varprod_divides(varprod_t *p1, varprod_t *p2) {
  return varexp_array_divides(p1->prod, p1->len, p2->prod, p2->len);
}

bool varprod_divisor(vpbuffer_t *b, varprod_t *p1, varprod_t *p2) {
  int32_t i, j, n, v;
  varexp_t *a1, *a2;

  n = p1->len;
  if (n > p2->len) return false;

  vpbuffer_set_varprod(b, p2);
  vpbuffer_pushback(b, INT32_MAX, INT32_MAX); // add an end marker

  a1 = p1->prod;
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
