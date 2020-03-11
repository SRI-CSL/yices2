/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
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
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

#include "solvers/cdcl/wide_truth_tables.h"


/*
 * 2^n for 32bit unsigned numbers
 */
static inline uint32_t pow2(uint32_t n) {
  assert(n < 32);
  return ((uint32_t) 1) << n;
}


#ifndef NDEBUG
/*
 * Check that all elements in w->val are 0 or 1
 */
static bool good_wide_ttbl_values(const wide_ttbl_t *w) {
  uint32_t i, n;

  assert(w->nvars < 32);
  n = ((uint32_t) 1) << w->nvars; // 2^nvars
  for (i=0; i<n; i++) {
    if (w->val[i] != 0 && w->val[i] != 1) return false;
  }
  return true;
}
#endif

/*
 * Multiply m by bit
 * - return 0 if bit == 0 or mask if bit == 1
 */
static inline uint32_t mask(uint32_t m, uint8_t bit) {
  assert(bit == 0 || bit == 1);
  return  m & (- (uint32_t) bit);
}


/*
 * Convert a wide truth table w to key/ttbl
 * - store four variables in v[0 ... v3] (copied from w->var)
 * - return a 16bit encoding of w->val as ttbl
 * - w must not have more than four variables
 *
 * Warning: if w stores a table for f(x0, .., x3) then
 * the value of f(b0, b1, b2, b3) is stored in w->val[i]
 * where i = b0 + 2 b1 + 4 b2 + 8 b3.
 * In the gmap, we store the same value in bit j of the ttbl
 * where j = 8 b0 + 4 b1 + 2 b2 + b3.
 */
static uint32_t convert_wide_ttbl(bvar_t v[4], const wide_ttbl_t *w) {
  uint32_t ttbl;

  assert(good_wide_ttbl_values(w));

  switch (w->nvars) {
  case 0:
    v[0] = null_bvar;
    v[1] = null_bvar;
    v[2] = null_bvar;
    v[3] = null_bvar;
    ttbl = mask(0xFFFF, w->val[0]);
    break;

  case 1:
    v[0] = w->var[0];
    v[1] = null_bvar;
    v[2] = null_bvar;
    v[3] = null_bvar;
    ttbl = mask(0x00FF, w->val[0]) | mask(0xFF00, w->val[1]);
    break;

  case 2:
    v[0] = w->var[0];
    v[1] = w->var[1];
    v[2] = null_bvar;
    v[3] = null_bvar;
    ttbl = mask(0x000F, w->val[0]) | mask(0x00F0, w->val[2])
      | mask(0x0F00, w->val[1]) | mask(0xF000, w->val[3]);
    break;

  case 3:
    v[0] = w->var[0];
    v[1] = w->var[1];
    v[2] = w->var[2];
    v[3] = null_bvar;
    ttbl = mask(0x0003, w->val[0]) | mask(0x000C, w->val[4])
      | mask(0x0030, w->val[2]) | mask(0x00C0, w->val[6])
      | mask(0x0300, w->val[1]) | mask(0x0C00, w->val[5])
      | mask(0x3000, w->val[3]) | mask(0xC000, w->val[7]);
    break;

  default:
    assert(w->nvars == 4);
    v[0] = w->var[0];
    v[1] = w->var[1];
    v[2] = w->var[2];
    v[3] = w->var[3];
    ttbl = mask(0x0001, w->val[0]) | mask(0x0002, w->val[8])
      | mask(0x0004, w->val[4]) | mask(0x0008, w->val[12])
      | mask(0x0010, w->val[2]) | mask(0x0020, w->val[10])
      | mask(0x0040, w->val[6]) | mask(0x0080, w->val[14])
      | mask(0x0100, w->val[1]) | mask(0x0200, w->val[9])
      | mask(0x0400, w->val[5]) | mask(0x0800, w->val[13])
      | mask(0x1000, w->val[3]) | mask(0x2000, w->val[11])
      | mask(0x4000, w->val[7]) | mask(0x8000, w->val[15]);
    break;
  }

  return ttbl;
}

/*
 * Print a table
 */
static void print_table(wide_ttbl_t *table) {
  uint32_t i, j, n, m;
  uint32_t bit;

  n = table->nvars;

  if (n == 0) {
    printf("constant function: %d\n", (int) table->val[0]);
  } else {
    for (i=0; i<n; i++) {
      printf("  x%"PRId32, table->var[i]);
    }
    printf("\n");

    m = pow2(n);
    for (j=0; j<m; j++) {
      for (i=0; i<n; i++) {
	bit = j & pow2(i);
	assert(bit == 0 || bit == pow2(i));
	if (bit == 0) {
	  printf("   0"); 
	} else {
	  printf("   1");
	}
      }
      assert(table->val[j] == 0 || table->val[j] == 1);
      printf("   |  %d\n", (int) table->val[j]);
    }
  }
  printf("\n");
}

/*
 * Store a function in table
 * - n = number of variables (must be 5 or less)
 * - v = array of n variables
 * - f = bitmask for the truth table (between 0 and 2^n-1)
 */
static void import_function(wide_ttbl_t *table, uint32_t n, const int32_t *v, uint32_t f) {
  uint32_t i, p;

  assert(n <= table->size && n <= 5);

  table->nvars = n;
  for (i=0; i<n; i++) {
    table->var[i] = v[i];
  }

  p = pow2(n);
  for (i=0; i<p; i++) {
    table->val[i] = f & 1;
    f >>= 1;
  }
}

/*
 * Get bit i of x (0 <= i < 16)
 */
static uint32_t get_bit(uint32_t x, uint32_t i) {
  assert(i < 16);
  return (x >> i) & 1;
}

/*
 * Project index i (0 <= i < 16) to n variables (n <= 4) 
 */
static uint32_t project_index(uint32_t i, uint32_t n) {
  uint32_t a[4];
  uint32_t b[4];
  uint32_t k, r, c;

  assert(n <= 4);

  // a[k] = bit k of i
  for (k=0; k<4; k++) {
    a[k] = get_bit(i, k);
  }

  // b[0 .. n-1] = a[3 .. 4-n]
  // r = b[0] + 2 b[1] + ... + 2^(n-1) b[n-1]
  c = 1;
  r = 0;
  for (k=0; k<n; k++) {
    b[k] = a[3 - k];
    r += b[k] * c;
    c <<= 1;
  }
  
  assert(r < pow2(n));

  return r;
}


/*
 * Check that g represents the same function as w
 * - g is interpreted using the gmap convention
 */
static bool check_functions(const wide_ttbl_t *w, uint32_t g) {
  uint32_t i, j, n;

  n = w->nvars;

  assert(n <= 4);
  for (i=0; i<16; i++) {
    j = project_index(i, n);
    if (get_bit(g, i) != w->val[j]) {
      return false;
    }
  }
  return true;
}


/*
 * Test: import function f of four variables then export it.
 */
static void test_import_export(wide_ttbl_t *table, uint32_t f) {
  wide_ttbl_t normal;
  int32_t v[4] = { 1, 2, 3, 4 };
  int32_t u[4];
  uint32_t ttbl;
  uint32_t i;

  assert(f <= (uint32_t) 0xFFFF);
  printf("test function: 0x%04x\n", (unsigned) f);
  import_function(table, 4, v, f);
 
  init_wide_ttbl(&normal, 4);
  if (! wide_ttbl_normalize(&normal, table)) {
    printf("*** Normalize failed ***\n");
    exit(1);
  }

  ttbl = convert_wide_ttbl(u, &normal);
  if (! check_functions(&normal, ttbl)) {
    printf("*** Export failed ***\n");
    printf("  export = 0x%04x\n", (unsigned) ttbl);    
    exit(1);
  } else {
    printf("\nNormalized table\n");
    print_table(&normal);
    printf("Export: var = [");
    for (i=0; i<4; i++) {
      printf(" %"PRId32, u[i]);
    }
    printf(" ] ttbl = 0x%04x\n\n", ttbl);
  }

  delete_wide_ttbl(&normal);
}

int main(void) {
  wide_ttbl_t test;
  uint32_t i;

  init_wide_ttbl(&test, 4);
  for (i=0; i<= 0xFFFF; i++) {
    test_import_export(&test, i);
  }
  delete_wide_ttbl(&test);

  return 0;
}
