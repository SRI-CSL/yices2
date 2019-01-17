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

  p = ((uint32_t) 1) << n; // 2^n 
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
 * Import a regular ttbl into w.
 * - w->size must be at least ttbl->nvars.
 * - ttbl must be normalized
 */
void wide_ttbl_import(wide_ttbl_t *w, const ttbl_t *ttbl) {
  uint32_t i, n, mask;

  assert(w->size >= ttbl->nvars);

  n = ttbl->nvars;
  w->nvars = n;
  for (i=0; i<n; i++) {
    w->var[i] = ttbl->label[i];
  }

  switch (n) {
  case 0:
    assert(ttbl->mask == 0x00 || ttbl->mask == 0xff);
    ttbl->val[0] = ttbl->mask & 1;
    break;
    
  case 1:
    assert(ttbl->mask == 0x0f || ttbl->mask == 0xf0);
    ttbl->val[0] = ttbl->mask & 1;
    ttbl->val[1] = (ttbl->maks >> 4) & 1;
    break;
      
  case 2:
    ttbl->val[0] = ttbl->mask & 1;
    ttbl->val[1] = (ttbl->mask >> 2) & 1;
    ttbl->val[2] = (ttbl->mask >> 4) & 1;
    ttbl->val[3] = (ttbl->mask >> 6) & 1;
    break;

  default:
    assert(n == 3);
    mask = ttbl->mask;
    for (i=0; i<8; i++) {
      tbl->val[i] = mask & 1;
      mask >>= 1;
    }
    /*
      ttbl->val[0] = ttbl->mask & 1;
      ttbl->val[1] = (ttbl->mask >> 1) & 1;
      ttbl->val[2] = (ttbl->mask >> 2) & 1;
      ttbl->val[3] = (ttbl->mask >> 3) & 1;
      ttbl->val[4] = (ttbl->mask >> 4) & 1;
      ttbl->val[5] = (ttbl->mask >> 5) & 1;
      ttbl->val[6] = (ttbl->mask >> 6) & 1;
      ttbl->val[7] = (ttbl->mask >> 7) & 1;
    */
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
  return (i & mask) | ((i & ~mask) >> 1);
}

static inline uint32_t insert_bit(uint32_t i, uint32_t mask, uint32_t b) {
  assert(b == 0 || b == 1);
  return (i & mask) | ((-b) & (mask + 1)) | ((i & ~mask) << 1);
}

/*
 * Set variable v[i] to '0' or '1' in w1
 * - b = either 0 or 1
 */
static void wide_ttbl_compose0(wide_ttbl_t *w, const wide_ttbl_t *w1, uint32_t i, uint32_t b) {
  uint32_t j, n, p, mask;

  assert(b == 0 || b == 1);
  assert(i < w1->nvars);

  n = w1->nvars - 1;
  if (w->size < n ) return false;

  // copy variables
  w->nvars = n;
  for (j=0; j<i; j++) {
    w->var[j] = w1->var[j];
  }
  for (j=i+1; j<=n; j++) {
    w->var[j-1] = w1->var[j];
  }

  // truth values
  p = ((uint32_t) 1) << n;
  mask = (((uint32_t) 1) << i) - 1; // 2^i - 1
  for (j=0; j<p; j++) {
    w->val[j] = w1->val[insert_bit(j, mask, b)];
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
  assert(i < w1->nvars);

  switch (ttbl->nvars) {    
  case 0:
    assert(ttbl->mask == 0x00 || ttbl->mask == 0xff);
    return wide_ttbl_compose0(w, w1, i, ttbl->mask & 1);

  case 1:
    break;

  case 2:
    break;

  default:
    assert(ttbl->nvars == 3);
    break;
  }

  return false;
}

