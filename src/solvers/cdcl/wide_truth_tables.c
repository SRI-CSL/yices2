/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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

#include <assert.h>

#include "solvers/cdcl/wide_truth_tables.h"
#include "utils/memalloc.h"


#ifndef NDEBUG

/*
 * Check that a[0 ... n-1] is sorted in increasing order.
 */
static bool sorted_array(const bvar_t *a, uint32_t n) {
  uint32_t i;

  if (n > 0) {
    for (i=0; i<n-1; i++) {
      if (a[i+1] <= a[i]) return false;
    }
  }

  return true;
}

#endif


/*
 * 2^n for 32bit unsigned numbers
 */
static inline uint32_t pow2(uint32_t n) {
  assert(n < 32);
  return ((uint32_t) 1) << n;
}


/*
 * Initialize w for size = n.
 * - this allocates arrays var and val
 * - n must be no more than MAX_WIDE_TTBL_SIZE
 * - w is initialized to the constant false function:
 *   nvars = 0, val[0] = 0.
 */
void init_wide_ttbl(wide_ttbl_t *w, uint32_t n) {
  uint32_t p;
  
  assert(n <= MAX_WIDE_TTBL_SIZE);

  p = pow2(n);
  w->size = n;
  w->nvars = 0;
  w->var = (bvar_t *) safe_malloc(n * sizeof(bvar_t));
  w->val = (uint8_t *) safe_malloc(p * sizeof(uint8_t));
  w->val[0] = 0;
}

/*
 * Delete w: free memory
 */
void delete_wide_ttbl(wide_ttbl_t *w) {
  safe_free(w->var);
  safe_free(w->val);
  w->var = NULL;
  w->val = NULL;
}

/*
 * Reset w to the constant false function
 */
void reset_wide_ttbl(wide_ttbl_t *w) {
  w->nvars = 0;
  w->val[0] = 0;
}


/*
 * Expand an 8-bit truth-table into bit array a
 * - a must be large enough (i.e., at least 2^n elements where n = ttbl->nvars)
 *
 * Warning: for a ttbl of 3 vars, f(x0, x1, x2) is encoded in bit i of
 * the mask where i = 4 x0 + 2 x1 + x2.
 * Here we want a[x0 + 2 x1 + 4 x2] = f(x0, x1, x2).
 */
static void expand_ttbl(uint8_t *a, const ttbl_t *ttbl) {
  uint32_t m;

  m = ttbl->mask;
  switch (ttbl->nvars) {
  case 0:
    assert(m == 0x00 || m == 0xff);
    a[0] = m & 1;
    break;
    
  case 1:
    assert(m == 0x0f || m == 0xf0);
    a[0] = m & 1; m >>= 4;
    a[1] = m & 1;
    break;
      
  case 2:
    a[0] = m & 1; m >>= 2;  // 00 --> 00
    a[2] = m & 1; m >>= 2;  // 01 --> 10
    a[1] = m & 1; m >>= 2;  // 10 --> 01
    a[3] = m & 1;           // 11 --> 11
    break;

  default:
    assert(ttbl->nvars == 3);
    a[0] = m & 1; m >>= 1;  // 000 --> 000
    a[4] = m & 1; m >>= 1;  // 001 --> 100
    a[2] = m & 1; m >>= 1;  // 010 --> 010
    a[6] = m & 1; m >>= 1;  // 011 --> 110
    a[1] = m & 1; m >>= 1;  // 100 --> 001
    a[5] = m & 1; m >>= 1;  // 101 --> 101
    a[3] = m & 1; m >>= 1;  // 110 --> 011
    a[7] = m & 1;           // 111 --> 111
    break;
  }
}


/*
 * Bit juggling: we interpret i as a vector of 32 bits.
 * - mask is (2^k - 1) for some small 0 <= k <= 32
 * - remove_bit(i, mask): remove bit k from i
 * - insert_bit(i, mask, b): insert bit b at index k
 *
 * More precisely:
 *      i is [i_0 .. i_{k-1}   i_k  i_{k+1} .. i_31]
 * remove is [i_0 .. i_{k-1} i_{k+1} ... i_31     0]
 * insert is [i_0 .. i_{k-1}   b    i_k     .. i_30]
 *               
 */
static inline uint32_t remove_bit(uint32_t i, uint32_t mask) {
  return (i & mask) | ((i >> 1) & ~mask);
}

static inline uint32_t insert_bit(uint32_t i, uint32_t mask, uint32_t b) {
  assert(b == 0 || b == 1);
  return (i & mask) | ((-b) & (mask + 1)) | ((i & ~mask) << 1);
}


/*
 * select_bit(i, 2^k) = k-th bit of i
 */
static inline uint32_t select_bit(uint32_t i, uint32_t selector) {
  return (i & selector) != 0;
}

/*
 * Copy all variables of a into b except a[i].
 * - a: array on n variables
 * - b: array large enough for n-1 variables
 */
static void remove_var(bvar_t *b, const bvar_t *a, uint32_t n, uint32_t i) {
  uint32_t j;

  assert(i < n);

  for (j=0; j<i; j++) b[j] = a[j];
  for (j=i+1; j<n; j++) b[j-1] = a[j];
}


/*
 * Insert variables b[0 ... m-1] into array a. Store the result in c.
 * - a: array of n variables in increasing order
 * - b: array of m variables in increasing order
 * - c: array large enough for n+m variables
 * - mask: array of m elements
 *
 * When inserting x = b[k], we store a bit mask into mask[k]
 * and a selector mask into selector[k].
 * - selector k is 2^j where c[j] = x (i.e., bit index for x in array c)
 * - mask[k] is 0b1111...11 if x is present in a
 * - mask[k] = 2^j - 1 if x is not present in a
 *
 * Return the number of elements stored in c = n + m - number
 * elements of b that are already in a.
 */
static uint32_t merge_vars(bvar_t *c, const bvar_t *a, uint32_t n, const bvar_t *b,
			   uint32_t m, uint32_t *mask, uint32_t *selector) {
  uint32_t i, j, k, s;
  bvar_t x;

  assert(sorted_array(a, n));
  assert(sorted_array(b, m));

  i = 0;
  j = 0;

  for (k=0; k<m; k++) {
    x = b[k];
    while (i < n && a[i] < x) c[j++] = a[i++];

    // x will be stored in c[j]
    s = pow2(j);
    selector[k] = s;              // 2^j
    mask[k] = ~((uint32_t) 0);   // default mask
    if (i == n || a[i] != x) {
      // x is not in array a
      mask[k] = s - 1;
      c[j++] = x;
    }
  }

  while (i < n) c[j++] = a[i++];

  assert(sorted_array(c, j));

  return j;
}


/*
 * Copy a into b
 */
static void copy_vars(bvar_t *b, const bvar_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) b[i] = a[i];
}

/*
 * Copy array value a into b: n = number of variables
 */
static void copy_values(uint8_t *b, const uint8_t *a, uint32_t n) {
  uint32_t i, p;

  p = pow2(n);
  for (i=0; i<p; i++) b[i] = a[i];
}

/*
 * Import a regular ttbl into w.
 * - w->size must be at least ttbl->nvars.
 * - ttbl must be normalized
 */
void wide_ttbl_import(wide_ttbl_t *w, const ttbl_t *ttbl) {
  assert(w->size >= ttbl->nvars);
  assert(sorted_array(ttbl->label, ttbl->nvars));

  w->nvars = ttbl->nvars;
  copy_vars(w->var, ttbl->label, ttbl->nvars);
  expand_ttbl(w->val, ttbl);
}

/*
 * Copy w1 into w
 * - w->size must be at least w1->size
 */
void wide_ttbl_copy(wide_ttbl_t *w, const wide_ttbl_t *w1) {
  assert(w->size >= w1->nvars);
  assert(sorted_array(w1->var, w1->nvars));

  w->nvars = w1->nvars;
  copy_vars(w->var, w1->var, w1->nvars);
  copy_values(w->val, w1->val, w1->nvars);
}


/*
 * Build a composed truth table:
 * - b = array of 2^n elements (to store the result)
 * - n = number of variables in the composed function
 * - a = truth table for some function f(x_0,.., x_i, ...)
 * - i = index of a variable x_0 ... x_m
 * - ttbl = a function g(y_0, ...y_k-1) (with k <= 3)
 * - mask and selector indicate how to locate and handle y_0, ..., y_{k-1}.
 *
 * This function builds the truth table for f(x_0..., g(y_0, ...,
 * y_{k-1}), ...): where x_i is replaced by g(y_0, ..., y_{k-1}).
 *
 * Let z_0, ..., z_{n-1} denote the set of variables in the
 * composition, listed in increasing order. Then we have
 *   { z_0, ..., z_{n-1} } = ( { x_0, ... , x_m } - { x_i } )
 *                         U { y_0, ... y_{k-1} }
 *
 * Variable y_t is then equal to some z_u and
 * - selector[t] is 2^u
 * - mask[t] is either (2^u - 1) or 0b111...1:
 *   mask[t] is (2^u - 1) if y_t is a not in {x_0, ..., x_m } - { x_i }.
 *   mask[t] is 0b111....1 otherwise
 *
 * The resulting truth table is stored in array b
 */
static void compose_truth_tables(uint8_t *b, uint32_t n, const uint8_t *a, uint32_t i,
				 const ttbl_t *ttbl, const uint32_t *mask, const uint32_t *selector) {
  uint32_t j, t, p, k, i_mask;
  uint8_t g[8];


  assert(i <= n && n <= MAX_WIDE_TTBL_SIZE);

  expand_ttbl(g, ttbl);
  p = pow2(n);
  i_mask = pow2(i) - 1;

  switch (ttbl->nvars) {
  case 0:
    for (j=0; j<p; j++) {
      t = insert_bit(j, i_mask, g[0]);
      b[j] = a[t];
    }
    break;

  case 1:
    for (j=0; j<p; j++) {
      k = select_bit(j, selector[0]);
      assert(k < 2);
      t = remove_bit(j, mask[0]);
      t = insert_bit(t, i_mask, g[k]);
      b[j] = a[t];
    }
    break;

  case 2:
    for (j=0; j<p; j++) {
      k = select_bit(j, selector[0]) | (select_bit(j, selector[1]) << 1);
      assert(k < 4);
      t = remove_bit(remove_bit(j, mask[1]), mask[0]);
      t = insert_bit(t, i_mask, g[k]);
      b[j] = a[t];
    }
    break;

  default:
    assert(ttbl->nvars == 3);
    for (j=0; j<p; j++) {
      k = select_bit(j, selector[0]) | (select_bit(j, selector[1]) << 1) | (select_bit(j, selector[2]) << 2);
      assert(k < 8);
      t = remove_bit(remove_bit(remove_bit(j, mask[2]), mask[1]), mask[0]);
      t = insert_bit(t, i_mask, g[k]);
      b[j] = a[t];
    }
    break;
  }

}

/*
 * Composition:
 * - w1 stores a function f(x0,..., x_k)
 * - ttbl stores another function g(y0, y1, y2).
 * - i is an index between 0 and k
 *
 * This function computes the truth table for 
 *   f(x_0,..., x_i-1, g(y0, y1, y2), x_{i+1}, ... x_k).
 * and stores it into w. This replaces x_i by g(y0, y1, y2) in f.
 *
 * The structure w must not be the same as w1.
 *
 * The function returns false if the composition can't be stored
 * in w (because it requires more variables than w->size).
 * If returns true otherwisw.
 */
bool wide_ttbl_compose(wide_ttbl_t *w, const wide_ttbl_t *w1, const ttbl_t *ttbl, uint32_t i) {
  bvar_t a[MAX_WIDE_TTBL_SIZE];
  bvar_t b[MAX_WIDE_TTBL_SIZE + 2];
  uint32_t mask[3];
  uint32_t selector[3];
  uint32_t n;

  assert(i < w1->nvars && w1->nvars <= MAX_WIDE_TTBL_SIZE);

  remove_var(a, w1->var, w1->nvars, i);
  n = merge_vars(b, a, w1->nvars - 1, ttbl->label, ttbl->nvars, mask, selector);

  /*
   * At this point:
   * - b = variables of w
   * - n = number of variables in v
   * - mask = masks for the variables of ttbl in b
   * - selector = positions of the variables of ttbl in b
   */
  if (n <= w->size) {
    w->nvars = n;
    copy_vars(w->var, b, n);
    compose_truth_tables(w->val, n, w1->val, i, ttbl, mask, selector);
    return true;
  }

  return false;
}

/*
 * Composition variant
 * - w1 stores the  truth table for a function f(x0 .... x_k)
 * - ttbl stores the truth table for a functioon g(y0...)
 * - x is a variable
 *
 * If x occurs in x0 ... x_k, then this replaces x by g(y0...) in f and store the
 * result in w. Otherwise,  this copies w1 into w.
 *
 * The function returns false if the composition can't be stored
 * in w (because it requires more variables than w->size).
 * It returns true otherwise.
 */
bool wide_ttbl_var_compose(wide_ttbl_t *w, const wide_ttbl_t *w1, const ttbl_t *ttbl, bvar_t x) {
  uint32_t i;

  for (i=0; i< w1->nvars; i++) {
    if (w1->var[i] == x) {
      return wide_ttbl_compose(w, w1, ttbl, i);
    }
  }

  if (w->size >= w1->size) {
    wide_ttbl_copy(w, w1);
    return true;
  }

  return false;
}


/*
 * Check whether the truth table a[0 ... 2^n-1] is independent of
 * index i.
 * - n = number of variables
 * - i = index between 0 and n-1
 */
static bool redundant_index(const uint8_t *a, uint32_t n, uint32_t i) {
  uint32_t j, p, i_mask;
  uint32_t t, u;

  assert(i < n);

  i_mask = pow2(i) - 1;
  p = pow2(n-1);
  for (j=0; j<p; j++) {
    t = insert_bit(j, i_mask, 0);
    u = insert_bit(j, i_mask, 1);
    assert(t < pow2(n) && u < pow2(n));
    if (a[t] != a[u]) {
      return false;
    }
  }

  return true;
}


/*
 * Collect the non-redundant variables of a table
 * - a = array of n variable
 * - b = truth table (2^n elements)
 * - c = array to store the non-redundant variables
 * - mask = array to store a mask for all redundant variables
 * - return the number of variables stored in c
 */
static uint32_t filter_redundant_vars(bvar_t *c, const bvar_t *a, uint32_t n, const uint8_t *b, uint32_t *mask) {
  uint32_t i, j, k;

  assert(sorted_array(a, n));

  j = 0; // index in a
  k = 0; // index in mask
  for (i=0; i<n; i++) {
    if (redundant_index(b, n, i)) {
      mask[k] = pow2(i) - 1;
      k ++;
    } else {
      c[j] = a[i];
      j ++;
    }
  }

  assert(k + j == n);

  assert(sorted_array(c, j));

  return j;
}

/*
 * Add k bits to j as specified by an array of masks
 * - each mask is of the form (2^i - 1)
 * - the masks must be in strict increasing order
 */
static uint32_t insert_zeros(uint32_t i, uint32_t k, const uint32_t *mask) {
  uint32_t j;

  for (j=0; j<k; j++) {
    i = insert_bit(i, mask[j], 0);
  }
  return i;
}


/*
 * Remove redundant elements from a truth table a
 * - n = number of non-redundant indices
 * - k = number of redundant indices
 * - a = original truth-table  (2^ (n+k) elements)
 * - mask = array of k masks that correspond to the redundant indices
 *   1) each element of mask is of the form (2^i - 1) where i is a
 *      redundant index for a
 *   2) the masks are in strictly increasing order
 * - b = array to store the result (b must have 2^n elements)
 */
static void filter_truth_table(uint8_t *b, uint32_t n, const uint8_t *a, const uint32_t *mask, uint32_t k) {
  uint32_t i, p, t;

  p = pow2(n);
  for (i=0; i<p; i++) {
    t = insert_zeros(i, k, mask);
    assert(t < pow2(n + k));
    b[i] = a[t];
  }
}

/*
 * Normalize w1 and store the result in w
 * - remove the redundant variables of w1
 * - returns true if w1 is large enough to contain the result, false otherwise
 */
bool wide_ttbl_normalize(wide_ttbl_t *w, const wide_ttbl_t *w1) {
  bvar_t a[MAX_WIDE_TTBL_SIZE];
  uint32_t mask[MAX_WIDE_TTBL_SIZE];
  uint32_t n;

  assert(w1->nvars <= MAX_WIDE_TTBL_SIZE);

  n = filter_redundant_vars(a, w1->var, w1->nvars, w1->val, mask);
  assert(n <= w1->nvars);

  if (n <= w->size) {
    w->nvars = n;
    copy_vars(w->var, a, n);
    filter_truth_table(w->val, n, w1->val, mask, w1->nvars - n);
    return true;
  }

  return false;
}


