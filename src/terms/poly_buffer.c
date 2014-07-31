/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * POLYNOMIAL BUFFER
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "terms/poly_buffer.h"


/*
 * Initialize buffer with default m_size and i_size
 */
void init_poly_buffer(poly_buffer_t *buffer) {
  int32_t *tmp;
  uint32_t i;

  tmp = (int32_t *) safe_malloc(DEF_POLYBUFFER_ISIZE * sizeof(int32_t));
  for (i=0; i<DEF_POLYBUFFER_ISIZE; i++) {
    tmp[i] = -1;
  }
  buffer->index = tmp;
  buffer->i_size = DEF_POLYBUFFER_ISIZE;

  buffer->mono = alloc_monarray(DEF_POLYBUFFER_MSIZE);
  buffer->m_size = DEF_POLYBUFFER_MSIZE;
  buffer->nterms = 0;

  q_init(&buffer->aux);
}


/*
 * Delete buffer
 */
void delete_poly_buffer(poly_buffer_t *buffer) {
  safe_free(buffer->index);
  clear_monarray(buffer->mono, buffer->m_size);
  safe_free(buffer->mono);
  buffer->mono = NULL;
  buffer->index = NULL;
  q_clear(&buffer->aux);
}


/*
 * Reset the buffer: free all mpq_t objects it uses,
 * - reset the number of terms to zero
 * - clear all the indices
 */
void reset_poly_buffer(poly_buffer_t *buffer) {
  uint32_t i, n;
  int32_t x;

  // clear the indices
  n = buffer->nterms;
  for (i=0; i<n; i++) {
    x = buffer->mono[i].var;
    assert(0 <= x && x < buffer->i_size && buffer->index[x] == i);
    buffer->index[x] = -1;
  }

  clear_monarray(buffer->mono, n);
  buffer->nterms = 0;

  q_clear(&buffer->aux);
}



/*
 * Extend the index array and initialize the new elements to -1
 * - this makes sure the array is large enough to store index[x]
 * - this must be called only if x >= buffer->i_size
 */
static void poly_buffer_resize_index(poly_buffer_t *buffer, int32_t x) {
  int32_t *tmp;
  uint32_t i, n;

  assert(x >= buffer->i_size);

  // new size is max(old_size + 50%, x+1)
  n = buffer->i_size;
  n += n>>1;
  if (n <= x) {
    n = x+1;
  }

  if (n >= MAX_POLYBUFFER_ISIZE) {
    out_of_memory();
  }

  tmp = (int32_t *) safe_realloc(buffer->index, n * sizeof(int32_t));
  for (i=buffer->i_size; i<n; i++) {
    tmp[i] = -1;
  }

  buffer->index = tmp;
  buffer->i_size = n;

  assert(x < buffer->i_size);
}



/*
 * Increase the size of the monomial array by 50%
 */
static void poly_buffer_resize_mono(poly_buffer_t *buffer) {
  int32_t n;

  n = buffer->m_size + 1;
  n += n >> 1;
  assert(n > buffer->m_size);
  if (n >= MAX_POLYBUFFER_MSIZE) {
    out_of_memory();
  }

  buffer->mono = realloc_monarray(buffer->mono, buffer->m_size, n);
  buffer->m_size = n;
}



/*
 * Allocate a monomial:
 * - return its index in the monomial array
 * - make the array larger if needed
 */
static int32_t poly_buffer_alloc_mono(poly_buffer_t *buffer) {
  uint32_t i;

  i = buffer->nterms;
  if (i == buffer->m_size) {
    poly_buffer_resize_mono(buffer);
  }
  assert(i < buffer->m_size);
  buffer->nterms = i+1;

  return i;
}


/*
 * Get buffer->index[x]
 * - if i_size is too small, make the index array large enough
 */
static inline int32_t poly_buffer_get_index(poly_buffer_t *buffer, int32_t x) {
  assert(0 <= x && x < max_idx);
  if (x >= buffer->i_size) {
    poly_buffer_resize_index(buffer, x);
  }
  return buffer->index[x];
}


/*
 * Add monomial a * x to the buffer
 */
void poly_buffer_add_monomial(poly_buffer_t *buffer, int32_t x, rational_t *a) {
  int32_t i;

  i = poly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->mono[i].var == x);
    q_add(&buffer->mono[i].coeff, a);
  } else {
    i = poly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->mono[i].var = x;
    q_set(&buffer->mono[i].coeff, a);
  }
}


/*
 * Add monomial b * a * x to the buffer
 */
void poly_buffer_addmul_monomial(poly_buffer_t *buffer, int32_t x, rational_t *a, rational_t *b) {
  int32_t i;

  i = poly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->mono[i].var == x);
    q_addmul(&buffer->mono[i].coeff, a, b);
  } else {
    i = poly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->mono[i].var = x;
    q_set(&buffer->mono[i].coeff, a);
    q_mul(&buffer->mono[i].coeff, b);
  }
}


/*
 * Subtract monomial a * x from the buffer
 */
void poly_buffer_sub_monomial(poly_buffer_t *buffer, int32_t x, rational_t *a) {
  int32_t i;

  i = poly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->mono[i].var == x);
    q_sub(&buffer->mono[i].coeff, a);
  } else {
    i = poly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->mono[i].var = x;
    q_set_neg(&buffer->mono[i].coeff, a);
  }
}


/*
 * Subtract monomial b * a * x to the buffer
 */
void poly_buffer_submul_monomial(poly_buffer_t *buffer, int32_t x, rational_t *a, rational_t *b) {
  int32_t i;

  i = poly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->mono[i].var == x);
    q_submul(&buffer->mono[i].coeff, a, b);
  } else {
    i = poly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->mono[i].var = x;
    q_set_neg(&buffer->mono[i].coeff, a);
    q_mul(&buffer->mono[i].coeff, b);
  }
}




/*
 * Add monomial 1 * x to the buffer
 */
void poly_buffer_add_var(poly_buffer_t *buffer, int32_t x) {
  int32_t i;

  i = poly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->mono[i].var == x);
    q_add_one(&buffer->mono[i].coeff);
  } else {
    i = poly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->mono[i].var = x;
    q_set_one(&buffer->mono[i].coeff);
  }
}


/*
 * Add monomial -1 * x to the buffer
 */
void poly_buffer_sub_var(poly_buffer_t *buffer, int32_t x) {
  int32_t i;

  i = poly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->mono[i].var == x);
    q_sub_one(&buffer->mono[i].coeff);
  } else {
    i = poly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->mono[i].var = x;
    q_set_minus_one(&buffer->mono[i].coeff);
  }
}



/*
 * Set coefficient of x equal to zero
 */
void poly_buffer_clear_monomial(poly_buffer_t *buffer, int32_t x) {
  int32_t i;

  assert(0 <= x && x < max_idx);
  if (x < buffer->i_size) {
    i = buffer->index[x];
    if (i >= 0) {
      q_clear(&buffer->mono[i].coeff);
    }
  }
}




/*
 * Add p to buffer
 */
void poly_buffer_add_poly(poly_buffer_t *buffer, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  for (i=0; i<n; i++) {
    poly_buffer_add_monomial(buffer, p->mono[i].var, &p->mono[i].coeff);
  }
}


/*
 * Subtract p from buffer
 */
void poly_buffer_sub_poly(poly_buffer_t *buffer, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  for (i=0; i<n; i++) {
    poly_buffer_sub_monomial(buffer, p->mono[i].var, &p->mono[i].coeff);
  }
}


/*
 * Add a * p to buffer
 */
void poly_buffer_addmul_poly(poly_buffer_t *buffer, polynomial_t *p, rational_t *a) {
  uint32_t i, n;

  n = p->nterms;
  for (i=0; i<n; i++) {
    poly_buffer_addmul_monomial(buffer, p->mono[i].var, &p->mono[i].coeff, a);
  }
}


/*
 * Subtract a * p from buffer
 */
void poly_buffer_submul_poly(poly_buffer_t *buffer, polynomial_t *p, rational_t *a) {
  uint32_t i, n;

  n = p->nterms;
  for (i=0; i<n; i++) {
    poly_buffer_submul_monomial(buffer, p->mono[i].var, &p->mono[i].coeff, a);
  }
}





/*
 * Get a pointer to the coefficient of x in buffer
 * - x must be between 0 and max_idx
 * - returns NULL if x does not occur in the buffer
 * - IMPORTANT: the pointer may become invalid after the next add/sub/addmul/submul
 */
rational_t *poly_buffer_var_coeff(poly_buffer_t *buffer, int32_t x) {
  int32_t i;

  assert(0 <= x && x < max_idx);
  if (x < buffer->i_size) {
    i = buffer->index[x];
    if (i >= 0) {
      return &buffer->mono[i].coeff;
    }
  }
  return NULL;
}



/*
 * Copy the coefficient of x into a
 * - x must be between 0 and max_idx.
 */
void poly_buffer_copy_var_coeff(poly_buffer_t *buffer, rational_t *a, int32_t x) {
  int32_t i;

  assert(0 <= x && x < max_idx);
  if (x < buffer->i_size) {
    i = buffer->index[x];
    if (i >= 0) {
      q_set(a, &buffer->mono[i].coeff);
      return;
    }
  }
  q_clear(a);
}




/*
 * NORMALIZATION
 */

/*
 * Add the end marker to the buffer
 * - nterms must not be incremented
 */
static void poly_buffer_add_end_marker(poly_buffer_t *buffer) {
  uint32_t i, n;

  i = buffer->nterms;
  n = buffer->m_size;
  if (i == n) {
    poly_buffer_resize_mono(buffer);
  }
  assert(i < buffer->m_size);
  buffer->mono[i].var = max_idx;
}



/*
 * Normalization:
 * - first clears all the indices
 * - then sort the monomials and remove all monomials with zero coefficient
 */
void normalize_poly_buffer(poly_buffer_t *buffer) {
  uint32_t i, n;
  int32_t x;

  // clear the indices
  n = buffer->nterms;
  for (i=0; i<n; i++) {
    x = buffer->mono[i].var;
    assert(0 <= x && x < buffer->i_size && buffer->index[x] == i);
    buffer->index[x] = -1;
  }

  // add the end-marker
  poly_buffer_add_end_marker(buffer);

  // sort and normalize
  assert(n == buffer->nterms);
  sort_monarray(buffer->mono, n);
  buffer->nterms = normalize_monarray(buffer->mono, n);

  // restore the indices
  n = buffer->nterms;
  for (i=0; i<n; i++) {
    x = buffer->mono[i].var;
    assert(0 <= x && x < buffer->i_size && buffer->index[x] == -1);
    buffer->index[x] = i;
  }
}



/*
 * Post-normalization: multiply all coefficients by -1
 */
void poly_buffer_negate(poly_buffer_t *buffer) {
  uint32_t i, n;

  n = buffer->nterms;
  for (i=0; i<n; i++) {
    q_neg(&buffer->mono[i].coeff);
  }
}



/*
 * Post-normalization: multiply all coefficients by a non-zero constant a
 */
void poly_buffer_rescale(poly_buffer_t *buffer, rational_t *a) {
  uint32_t i, n;

  assert(q_is_nonzero(a));

  n = buffer->nterms;
  for (i=0; i<n; i++) {
    q_mul(&buffer->mono[i].coeff, a);
  }
}



/*
 * Multiply by the inverse of the main coefficient: this makes the
 * main coefficient equal to one.
 * - return true is this the main coefficient was negative
 * - return false otherwise
 * The buffer must be non-zero
 */
bool poly_buffer_make_monic(poly_buffer_t *buffer) {
  monomial_t *a;
  rational_t *main_coeff;
  uint32_t i, n;
  bool negated;

  assert(buffer->nterms > 0);
  n = buffer->nterms - 1;
  a = buffer->mono;
  main_coeff = &a[n].coeff;

  assert(q_is_nonzero(main_coeff));

  if (q_is_one(main_coeff)) {
    // nothing to do
    return false;
  }

  if (q_is_minus_one(main_coeff)) {
    poly_buffer_negate(buffer);
    return true;
  }

  negated = q_is_neg(main_coeff);
  for (i=0; i<n; i++) {
    q_div(&a[i].coeff, main_coeff);
  }
  q_set_one(main_coeff);

  return negated;
}


/*
 * Remove all common factors from a[0] to a[n-1] (i.e.,
 * divide them by d = gcd(a[0], ..., a[n-1])
 * - if b is non NULL, divide it by d too
 * - a[0] to a[n-1] must all be integers
 */
static void reduce_integer_coeffs(monomial_t *a, uint32_t n, rational_t *b) {
  rational_t gcd;
  uint32_t i;

  assert(n > 0);

  q_init(&gcd);
  q_set_abs(&gcd, &a[0].coeff);
  for (i=1; i<n; i++) {
    q_gcd(&gcd, &a[i].coeff);
  }

  if (! q_is_one(&gcd)) {
    for (i=0; i<n; i++) {
      q_div(&a[i].coeff, &gcd);
    }
    if (b != NULL) {
      q_div(b, &gcd);
    }
  }

  q_clear(&gcd);
}


/*
 * Make all coefficients in a[0] to a[n-1] integral and make the main
 * coefficient positive by multiplying them by L = +/- lcm (den(a[0]), ..., den(a[n-1]))
 * Then remove common factors (i.e., divide a[0], ..., a[n-1] by D = gcd(a[0],..., a[n-1]))
 * - if b is non NULL multiply it by L/D too
 * - return true if L is negative, false otherwise
 * - n must be positive
 */
static bool scale_coeffs_to_integers(monomial_t *a, uint32_t n, rational_t *b) {
  rational_t lcm, den;
  uint32_t i;
  bool negated;

  assert(n > 0);

  // compute LCM
  q_init(&lcm);
  q_set_one(&lcm);
  q_init(&den);
  for (i=0; i<n; i++) {
    q_get_den(&den, &a[i].coeff);
    q_lcm(&lcm, &den);
  }

  negated = q_is_neg(&a[n-1].coeff);

  if (q_is_one(&lcm)) {

    // flip the signs to make the main coefficient positive
    if (negated) {
      for (i=0; i<n; i++) {
        q_neg(&a[i].coeff);
      }
      if (b != NULL) {
        q_neg(b);
      }
    }

  } else {

    // multiply by LCM
    if (negated) {
      q_neg(&lcm);
    }
    for (i=0; i<n; i++) {
      q_mul(&a[i].coeff, &lcm);
    }
    if (b != NULL) {
      q_mul(b, &lcm);
    }

  }

  // remove common factors
  reduce_integer_coeffs(a, n, b);

#ifndef NDEBUG
  for (i=0; i<n; i++) {
    assert(q_is_integer(&a[i].coeff));
  }
  assert(q_is_pos(&a[n-1].coeff));
#endif

  q_clear(&lcm);
  q_clear(&den);

  return negated;
}

/*
 * Make all coefficients integral and the main coefficient positive
 * by multiplying by a L = +/- lcm of coefficient denominators
 * - return true is L is negative, false otherwise
 * - the buffer must be non-zero
 */
bool poly_buffer_make_integral(poly_buffer_t *buffer) {
  assert(buffer->nterms > 0);
  return scale_coeffs_to_integers(buffer->mono, buffer->nterms, NULL);
}


/*
 * Make all coefficients integral, except possibly the constant term.
 * Make the main coefficient positive.
 */
bool poly_buffer_make_nonconstant_integral(poly_buffer_t *buffer) {
  monomial_t *a;
  rational_t *constant;
  uint32_t n;

  assert(buffer->nterms > 0);

  a = buffer->mono;
  n = buffer->nterms;
  constant = NULL;
  if (a->var == const_idx) {
    // keep a pointer to the constant
    constant = &a->coeff;
    a ++;
    n --;
    // if no other terms, make the constant positive
    if (n == 0) {
      if (q_is_neg(constant)) {
        q_neg(constant);
        return true;
      }
      return false;
    }
  }

  return scale_coeffs_to_integers(a, n, constant);
}






/*
 * SUBSTITUTION
 */

/*
 * Subtract a * row from buffer: row is a matrix row
 */
static void poly_buffer_submul_row(poly_buffer_t *buffer, row_t *row, rational_t *a) {
  uint32_t i, n;
  int32_t x;

  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      poly_buffer_submul_monomial(buffer, x, &row->data[i].coeff, a);
    }
  }
}


/*
 * Add row to buffer: special form of submul when a = -1
 */
static void poly_buffer_add_row(poly_buffer_t *buffer, row_t *row) {
  uint32_t i, n;
  int32_t x;

  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      poly_buffer_add_monomial(buffer, x, &row->data[i].coeff);
    }
  }
}


/*
 * Subtract row from buffer: special form of submul when a = 1
 */
static void poly_buffer_sub_row(poly_buffer_t *buffer, row_t *row) {
  uint32_t i, n;
  int32_t x;

  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      poly_buffer_sub_monomial(buffer, x, &row->data[i].coeff);
    }
  }
}

/*
 * Substitute basic variables in buffer
 * - matrix must be in tableau form
 * - if y is a basic variable in matrix, then it occurs in a single row
 *   of the form (y + a_1 x_1 + ... + a_n x_n) = 0
 * - the function replaces y by - (a_1 x_1 + ... + a_n x_n) in buffer,
 *   for all basic variables y.
 */
void poly_buffer_substitution(poly_buffer_t *buffer, matrix_t *matrix) {
  row_t *row;
  rational_t *a;
  uint32_t i, n;
  int32_t y, r;

  // First collect all the indices
  n = buffer->nterms;

  for (i=0; i<n; i++) {
    /*
     * Operations inside this loop change mono but they
     * don't change mono[0].var ... mono[n-1].var.
     */
    y = buffer->mono[i].var;
    r = matrix_basic_row(matrix, y);
    if (r >= 0) {
      row = matrix_row(matrix, r);
      a = &buffer->mono[i].coeff;
      /*
       * a.y is a monomial in buffer where y is a basic variable.
       * row is of the form (y + terms) == 0.
       * we subtract a * (y + terms) to eliminate y from buffer
       */
      if (q_is_one(a)) {
        poly_buffer_sub_row(buffer, row);
      } else if (q_is_minus_one(a)) {
        poly_buffer_add_row(buffer, row);
      } else if (q_is_nonzero(a)) {
        // we need to make a copy of a since a --> mono[i].coeff
        // and it mono[i].coeff will be reset to 0
        q_set(&buffer->aux, a);
        poly_buffer_submul_row(buffer, row, &buffer->aux);
      }
    }
  }
}






/*
 * GCD test: check whether (b + a_1 x_1 + ... + a_n x_n) can be zero
 * - a_1, ..., a_n and b must all be integer constants
 * - x_1, ..., x_n must be integer variables
 */
bool poly_buffer_gcd_test(poly_buffer_t *buffer) {
  monomial_t *a;
  rational_t gcd;
  bool divides;
  uint32_t i, n;

  a = buffer->mono;
  n = buffer->nterms;
  if (n == 0 || a->var != const_idx) return true; // the constant is 0
  if (n == 1) return false;  // poly is a non-zero constant

  assert(n >= 2);

  // compute gcd(a[1], ..., a[n])
  q_init(&gcd);
  q_set(&gcd, &a[1].coeff);
  for (i=2; i<n; i++) {
    q_gcd(&gcd, &a[i].coeff);
    // could exit as soon as gcd is 1?
  }

  // the constant term is a[0].coeff
  divides = q_integer_divides(&gcd, &a->coeff);
  q_clear(&gcd);
  return divides;
}

/*
 * Copy the constant term of buffer into a
 */
void poly_buffer_get_constant(poly_buffer_t *buffer, rational_t *a) {
  if (buffer->nterms > 0 && buffer->mono[0].var == const_idx) {
    q_set(a, &buffer->mono[0].coeff);
  } else {
    q_clear(a);
  }
}


/*
 * Copy the opposite of the constant term of buffer into a
 */
void poly_buffer_get_neg_constant(poly_buffer_t *buffer, rational_t *a) {
  if (buffer->nterms > 0 && buffer->mono[0].var == const_idx) {
    q_set_neg(a, &buffer->mono[0].coeff);
  } else {
    q_clear(a);
  }
}


/*
 * Build the LCM of denominators of coefficients of buffer
 */
void poly_buffer_get_den_lcm(poly_buffer_t *buffer, rational_t *a) {
  uint32_t i, n;
  monomial_t *mono;
  rational_t den;

  n = buffer->nterms;
  mono = buffer->mono;
  q_init(&den);
  q_set_one(a);
  for (i=0; i<n; i++) {
    q_get_den(&den, &mono[i].coeff);
    q_lcm(a, &den);
  }
  q_clear(&den);
}


/*
 * Check whether the non-constant part of buffer is reduced to a single variable
 * or equal to 0 (i.e., the buffer is either a + x or x, where a
 * is a constant).
 * - if so return x, otherwise return null_idx = -1
 */
int32_t poly_buffer_nonconstant_convert_to_var(poly_buffer_t *buffer) {
  uint32_t n;
  int32_t x;

  n = buffer->nterms;
  if (n == 1) {
    if (q_is_one(&buffer->mono[0].coeff)) {
      x = buffer->mono[0].var;
      return (x == const_idx) ? null_idx : x;
    } else {
      return null_idx;
    }
  } else if (n == 2) {
    if (buffer->mono[0].var == const_idx && q_is_one(&buffer->mono[1].coeff)) {
      return buffer->mono[1].var;
    } else {
      return null_idx;
    }
  } else {
    return null_idx;
  }
}


/*
 * Given p = content of buffer, check whether (p == 0) can be rewritten
 * to x = a where x is a variable and a is a rational constant.
 * - if so return the variable index x and copy the constant in a
 * - otherwise, return null_idx and leave a unchanged
 */
int32_t poly_buffer_convert_to_vareq(poly_buffer_t *buffer, rational_t *a) {
  uint32_t n;
  int32_t x;

  n = buffer->nterms;
  if (n == 1) {
    x = buffer->mono[0].var;
    if (x == const_idx) {
      return null_idx;

    } else {
      /*
       * p is b.x for some non-zero b
       * so p == 0 is equivalent to x == 0
       */
      assert(q_is_nonzero(&buffer->mono[0].coeff));
      q_clear(a);

      return x;
    }

  } else if (n == 2 && buffer->mono[0].var == const_idx) {
    /*
     * p is c + b x for some non-zero b and c
     * so p == 0 is equivalent to x == -c/b
     */
    x = buffer->mono[1].var;
    assert(q_is_nonzero(&buffer->mono[1].coeff));
    q_set_neg(a, &buffer->mono[0].coeff);
    q_div(a, &buffer->mono[1].coeff);

    return x;

  } else {
    return null_idx;
  }
}



/*
 * Create a polynomial equal to buffer then reset buffer.
 * - buffer must be normalized
 */
polynomial_t *poly_buffer_get_poly(poly_buffer_t *buffer) {
  polynomial_t *p;
  uint32_t i, n;
  int32_t x;

  // clear the indices
  n = buffer->nterms;
  for (i=0; i<n; i++) {
    x = buffer->mono[i].var;
    assert(0 <= x && x < buffer->i_size && buffer->index[x] == i);
    buffer->index[x] = -1;
  }

  p = monarray_get_poly(buffer->mono, buffer->nterms);
  buffer->nterms = 0;
  return p;
}
