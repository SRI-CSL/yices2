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
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

#include "solvers/cdcl/truth_tables.h"
#include "solvers/cdcl/wide_truth_tables.h"
#include "utils/int_vectors.h"


/*
 * 2^n for 32bit unsigned numbers
 */
static inline uint32_t pow2(uint32_t n) {
  assert(n < 32);
  return ((uint32_t) 1) << n;
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
 * Show function of 3 variables
 * - f = integer between 0 and 255
 */
static void show_function(uint32_t f, int32_t var[3]) {
  printf("  x%"PRId32"  x%"PRId32"  x%"PRId32"\n", var[0], var[1], var[2]);
  printf("   0   0   0   |  %"PRIu32"\n", f & 1);
  printf("   0   0   1   |  %"PRIu32"\n", (f >> 1) & 1);
  printf("   0   1   0   |  %"PRIu32"\n", (f >> 2) & 1);
  printf("   0   1   1   |  %"PRIu32"\n", (f >> 3) & 1);
  printf("   1   0   0   |  %"PRIu32"\n", (f >> 4) & 1);
  printf("   1   0   1   |  %"PRIu32"\n", (f >> 5) & 1);
  printf("   1   1   0   |  %"PRIu32"\n", (f >> 6) & 1);
  printf("   1   1   1   |  %"PRIu32"\n", (f >> 7) & 1);
  printf("\n");
}

/*
 * Truth table for a function of 3 variables.
 * - f = integer between 0 and 255
 */
static void set_function(ttbl_t *ttbl, uint32_t f, int32_t var[3]) {
  ttbl->nvars = 3;
  ttbl->label[0] = pos_lit(var[0]);
  ttbl->label[1] = pos_lit(var[1]);
  ttbl->label[2] = pos_lit(var[2]);
  ttbl->mask = f & 255;
  normalize_truth_table(ttbl);
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
 * Find index of x in array a[0...n-1]
 * - return -1 if it's not there
 */
static int32_t var_index_in_array(int32_t x, const int32_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] == x) return i;
  }
  return -1;
}


/*
 * Evaluate ttbl at a point defined by var[i] = val[i]
 * - var[] = array of n variables
 * - val[] = array of n values for these variables
 */
static uint32_t eval_ttbl(const ttbl_t *ttbl, uint32_t n, const int32_t *var, const uint8_t *val) {
  uint32_t k, i;
  int32_t idx;

  i = 0;
  for (k=0; k<n; k++) {
    idx = var_index_in_array(var[k], ttbl->label, ttbl->nvars);
    if (idx >= 0 && val[k] == 1) {
      assert(0 <= idx && idx <= 2);
      i += pow2(2 - idx);
    }
  }

  assert(i <= 7);

  return (ttbl->mask & pow2(i)) != 0;
}


/*
 * Evaluate table at a point: same conventions as above.
 * - the input is defined by n variables var[0] ... var[n-1]
 *   and by n values assigned to these variables: val[0] ... val[n-1].
 */
static uint32_t eval_table(const wide_ttbl_t *table, uint32_t n, const int32_t *var, const uint8_t *val) {
  uint32_t k, i;
  int32_t idx;

  assert(table->nvars <= 32);

  i = 0;
  for (k=0; k<n; k++) {
    idx = var_index_in_array(var[k], table->var, table->nvars);
    if (idx >= 0 && val[k] == 1) {
      assert(0 <= idx && idx < table->nvars);
      i += pow2(idx);
    }
  }

  assert(i < pow2(table->nvars));

  return table->val[i];
}


/*
 * Init an array val[n] as 0b0000
 */
static void init_val_array(uint8_t *val, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    val[i] = 0;
  }
}

/*
 * Increment val[n]
 */
static void next_val_array(uint8_t *val, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (val[i] == 0) break;
    assert(val[i] == 1);
    val[i] = 0;
  }

  if (i <= n) {
    val[i] = 1;
  } else {
    // reset to all zeros
    init_val_array(val, n);
  } 
}


/*
 * Show val array
 */
static void show_val_array(const uint8_t *val, uint32_t n) {
  uint32_t i;

  i = n;
  while (i > 0) {
    i --;
    assert(val[i] <= 1);
    fputc((int) ('0' + val[i]), stdout);
  }
}


/*
 * Compare ttbl and table: var[3] list all variables that can occur in either
 */ 
static void validate_import(const wide_ttbl_t *table, const ttbl_t *ttbl, const int32_t var[3]) {
  uint8_t val[3];
  uint32_t i, a, b;

  init_val_array(val, 3);
  for (i=0; i<8; i++) {
    printf("checking: ");
    show_val_array(val, 3);
    a = eval_ttbl(ttbl, 3, var, val);
    b = eval_table(table, 3, var, val);
    if (a != b) {
      fprintf(stderr, "*** BUG: bad import ***\n");
      fprintf(stderr, "value to ttbl = %"PRIu32"\n", a);
      fprintf(stderr, "value for table = %"PRIu32"\n", b);
      exit(1);
    }
    printf(" --> %"PRIu32"\n", a);
    next_val_array(val, 3);
  }
}


/*
 * Copy vars of a into vector v. Skip the i-th variable.
 * - n = size of a
 */
static void collect_vars(ivector_t *v, const int32_t *a, uint32_t n, uint32_t i) {
  uint32_t j;

  for (j=0; j<n; j++) {
    if (j != i) ivector_push(v, a[j]);
  }
}

/*
 * Check whether x is present in vector v
 */
static bool var_is_present(const ivector_t *v, int32_t x) {
  return var_index_in_array(x, v->data, v->size) >= 0;
}

/*
 * Append variables of a to vector v. Skip duplicaes
 */
static void append_vars(ivector_t *v, const int32_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (!var_is_present(v, a[i])) {
      ivector_push(v, a[i]);
    }
  }
}

/*
 * Copy values for composition:
 * - val[j] = v0[j] if 0 < j < i
 * - val[i] = b
 * - val[j+1] = v0[j] if i <= j < n
 */
static void compose_values(uint8_t *val, const uint8_t *v0, uint32_t n, uint32_t i, uint32_t b) {
  uint32_t j;

  assert(b == 0 || b == 1);
  assert(i <= n);

  for (j=0; j<i; j++) {
    val[j] = v0[j];
  }
  val[i] = b;
  for (j=i; j<n; j++) {
    val[j+1] = v0[j];
  }
}

/*
 * Check that table is the composition of table0 and ttbl
 */
static void validate_merge(const wide_ttbl_t *table, const wide_ttbl_t *table0, const ttbl_t *ttbl, uint32_t i) {
  ivector_t v;
  uint8_t val[16];
  uint8_t aux[16];
  uint32_t j, n, p, a, b, c;

  init_ivector(&v, 10);
  collect_vars(&v, table0->var, table0->nvars, i);
  append_vars(&v, ttbl->label, ttbl->nvars);

  n = v.size;

  assert(n < 16);

  p = pow2(n);

  init_val_array(val, n);
  for (j=0; j<p; j++) {
    printf("checking: ");
    show_val_array(val, n);
    a = eval_table(table, n, v.data, val);
    b = eval_ttbl(ttbl, n, v.data, val);
    compose_values(aux, val, table0->nvars - 1, i, b);
    c = eval_table(table0, table0->nvars, table0->var, aux);
    if (a != c) {
      fprintf(stderr, "*** BUG: bad merge ***\n");
      fprintf(stderr, "value for table = %"PRIu32"\n", a);
      fprintf(stderr, "value for  ttbl = %"PRIu32"\n", b);
      fprintf(stderr, "value for comp  = %"PRIu32"\n", c);
      exit(1);
    }
    printf(" --> %"PRIu32"\n", a);
    next_val_array(val, n);
  }

  delete_ivector(&v);
}



static void import(wide_ttbl_t *test, uint32_t f, int32_t var[3]) {
  ttbl_t ttbl;

  set_function(&ttbl, f, var);
  wide_ttbl_import(test, &ttbl);  
}

static void test_merge(wide_ttbl_t *test, uint32_t f, int32_t var[3]) {
  wide_ttbl_t result;
  ttbl_t ttbl;
  uint32_t i;

  printf("==== merge test ====\n");
  printf("function f:\n");
  show_function(f, var);
  printf("function g:\n");
  print_table(test);
  printf("\n");

  init_wide_ttbl(&result, 8);
  set_function(&ttbl, f, var);
  for (i=0; i<test->nvars; i++) {
    printf("replacing x%"PRId32" by f in g\n", test->var[i]);
    if (!wide_ttbl_compose(&result, test, &ttbl, i)) {
      printf("*** compose failed ***\n");
      exit(1);
    }
    print_table(&result);
    validate_merge(&result, test, &ttbl, i);
    printf("\n");    
  }

  delete_wide_ttbl(&result);
}


static void test_import(wide_ttbl_t *test, uint32_t f) {
  ttbl_t ttbl;
  int32_t v[3] = { 1, 2, 3 };

  printf("function 0x%02x\n", (unsigned) f);
  show_function(f, v);
  set_function(&ttbl, f, v);
  wide_ttbl_import(test, &ttbl);
  print_table(test);
  validate_import(test, &ttbl, v);
  printf("\n");
}


// normalize: 5 variables
static void test_normalize(wide_ttbl_t *test, uint32_t f) {
  wide_ttbl_t result;
  int32_t v[5] = { 1, 2, 3, 4, 5 };

  printf("==== normalize test ====\n");
  printf("function 0x%08x\n", (unsigned) f);
  import_function(test, 5, v, f);
  print_table(test);

  init_wide_ttbl(&result, 8);
  if (! wide_ttbl_normalize(&result, test)) {
    printf("*** normalize failed ***\n");
    exit(1);
  }
  print_table(&result);
  printf("\n");

  delete_wide_ttbl(&result);
}



int main(void) {
  wide_ttbl_t test;
  uint32_t i;
  bvar_t v[3];
  bvar_t u[3];

  init_wide_ttbl(&test, 6);
  for (i=0; i<256; i++) {
    test_import(&test, i);
  }

  v[0] = 2; v[1] = 4; v[2] = 5;
  import(&test, 0x2d, v);

  u[0] = 6; u[1] = 7; u[2] = 8;
  for (i=0; i<256; i++) {
    test_merge(&test, i, u);
  }
  u[0] = 4; u[1] = 6; u[2] = 7;
  for (i=0; i<256; i++) {
    test_merge(&test, i, u);
  }
  u[0] = 3; u[1] = 6; u[2] = 7;
  for (i=0; i<256; i++) {
    test_merge(&test, i, u);
  }
  u[0] = 1; u[1] = 3; u[2] = 6;
  for (i=0; i<256; i++) {
    test_merge(&test, i, u);
  }
  u[0] = 1; u[1] = 3; u[2] = 4;
  for (i=0; i<256; i++) {
    test_merge(&test, i, u);
  }
  u[0] = 1; u[1] = 4; u[2] = 5;
  for (i=0; i<256; i++) {
    test_merge(&test, i, u);
  }

  test_normalize(&test, 0x00000000u);
  test_normalize(&test, 0xFFFFFFFFu);
  test_normalize(&test, 0xAAAAAAAAu);
  test_normalize(&test, 0x55555555u);
  test_normalize(&test, 0xCCCCCCCCu);
  test_normalize(&test, 0x33333333u);
  test_normalize(&test, 0xF0F0F0F0u);
  test_normalize(&test, 0x0F0F0F0Fu);
  test_normalize(&test, 0xFF00FF00u);
  test_normalize(&test, 0x00FF00FFu);
  test_normalize(&test, 0xFFFF0000u);
  test_normalize(&test, 0x0000FFFFu);
  test_normalize(&test, 0xFFFF0000u ^ 0x33333333u);
  test_normalize(&test, 0x01234567u);

  delete_wide_ttbl(&test);

  return 0;
}
