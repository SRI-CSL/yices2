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

#include "solvers/cdcl/truth_tables.h"


/*
 * ELEMENTARY OPERATIONS ON TRUTH TABLES
 */

/*
 * We use the following operations to normalize a truth table:
 * - negate a column: if column i is labeled by (not x), then replace the
 *                    label by x and fix the bit mask (permutation)
 * - swap two adjacent columns
 * - remove irrelevant columns
 * - merge adjacent columns if they're labeled with the same variable
 * - remove column 0 if it's labeled with variable 0 (i.e., column 0 is the true constant)
 */

/*
 * negate column 0: input b7 b6 b5 b4 b3 b2 b1 b0
 *                 output b3 b2 b1 b0 b7 b6 b5 b4
 */
static inline uint8_t negate0(uint8_t b) {
  return (b & 0xf0) >> 4 | (b & 0x0f) << 4;
}

/*
 * negate column 1: input b7 b6 b5 b4 b3 b2 b1 b0
 *                 output b5 b4 b7 b6 b1 b0 b3 b2
 */
static inline uint8_t negate1(uint8_t b) {
  return (b & 0xcc) >> 2 | (b & 0x33) << 2;
}

/*
 * negate column 2: input b7 b6 b5 b4 b3 b2 b1 b0
 *                 output b6 b7 b4 b5 b2 b3 b0 b1
 */
static inline uint8_t negate2(uint8_t b) {
  return (b & 0xaa) >> 1 | (b & 0x55) << 1;
}

/*
 * swap columns 0 and 1: input b7 b6 b5 b4 b3 b2 b1 b0
 *                      output b7 b6 b3 b2 b5 b4 b1 b0
 */
static inline uint8_t swap01(uint8_t b) {
  return (b & 0xc3) | (b & 0x0c) << 2 | (b & 0x30) >> 2;
}

/*
 * swap columns 1 and 2: input b7 b6 b5 b4 b3 b2 b1 b0
 *                      output b7 b5 b6 b4 b3 b1 b2 b0
 */
static inline uint8_t swap12(uint8_t b) {
  return (b & 0x99) | (b & 0x22) << 1 | (b & 0x44) >> 1;
}

/*
 * remove column 0 (when true):
 *   input b7 b6 b5 b4 b3 b2 b1 b0
 *  output b7 b7 b6 b6 b5 b5 b4 b4
 */
static inline uint8_t force_true0(uint8_t b) {
  return (b & 0x80) | (b & 0xc0) >> 1 | (b & 0x60) >> 2 | (b & 0x30) >> 3 | (b & 0x10) >> 4;

}

/*
 * merge column 0 and 1 (equal labels)
 *   input b7 b6 b5 b4 b3 b2 b1 b0
 *  output b7 b7 b6 b6 b1 b1 b0 b0
 */
static inline uint8_t merge01(uint8_t b) {
  return (b & 0x81) | (b & 0xc0) >> 1 | (b & 0x40) >> 2 | (b & 0x02) << 2 | (b & 0x03) << 1;
}

/*
 * merge column 1 and 2 (equal labels)
 *   input: b7 b6 b5 b4 b3 b2 b1 b0
 *  output: b7 b7 b4 b4 b3 b3 b0 b0
 */
static inline uint8_t merge12(uint8_t b) {
  return (b & 0x99) | (b & 0x88) >> 1 | (b & 0x11) << 1;
}

/*
 * Check whether column 0 is irrelevant
 * - i.e. whether (b7 b6 b5 b4) == (b3 b2 b1 b0)
 */
static inline bool irrelevant0(uint8_t b) {
  return (b & 0x0f) == (b >> 4);
}

/*
 * Check whether column 1 is irrelevant (i.e., (b5 b4 b1 b0) == (b7 b6 b3 b2)
 */
static inline bool irrelevant1(uint8_t b) {
  return (b & 0x33) == (b & 0xcc) >> 2;
}

/*
 * Check whether column 2 is irrelevant (i.e., (b7 b5 b3 b1) == (b6 b4 b2 b0)
 */
static inline bool irrelevant2(uint8_t b) {
  return (b & 0x55) == (b & 0xaa) >> 1;
}


/*
 * Remove irrelevant columns
 */
// input: b3 b2 b1 b0 b3 b2 b1 b0 --> b3 b3 b2 b2 b1 b1 b0 b0
static inline uint8_t remove0(uint8_t b) {
  assert(irrelevant0(b));
  return (b & 0x81) | (b & 0xc0) >> 1 | (b & 0x60) >> 2 | (b & 0x03) << 1;
}

// input b3 b2 b3 b2 b1 b0 b1 b0 --> b3 b3 b2 b2 b1 b1 b0 b0
static inline uint8_t remove1(uint8_t b) {
  assert(irrelevant1(b));
  return (b & 0x99) | (b & 0x22) << 1 | (b & 0x44) >> 1;
}

// input: b3 b3 b2 b2 b1 b1 b0 b0 --> no change
static inline uint8_t remove2(uint8_t b) {
  assert(irrelevant2(b));
  return b;
}


/*
 * For debugging: check that tt is normalized
 */
#ifndef NDEBUG
static bool normal_truth_table(const ttbl_t *tt) {
  switch (tt->nvars) {
  case 0:
    return tt->label[0] == null_bvar && tt->label[1] == null_bvar &&
      tt->label[2] == null_bvar && (tt->mask == 0x00 || tt->mask == 0xff);

  case 1:
    return tt->label[0] > const_bvar && tt->label[1] == null_bvar &&
      tt->label[2] == null_bvar && (tt->mask == 0xf0 || tt->mask == 0x0f);

  case 2:
    return tt->label[0] > const_bvar && tt->label[1] > tt->label[0] &&
      tt->label[2] == null_bvar && !irrelevant0(tt->mask) &&
      !irrelevant1(tt->mask) && irrelevant2(tt->mask);

  case 3:
    return tt->label[0] > const_bvar && tt->label[1] > tt->label[0] &&
      tt->label[2] > tt->label[1] && !irrelevant0(tt->mask) &&
      !irrelevant1(tt->mask) && !irrelevant2(tt->mask);

  default:
    return false;
  }
}

#endif


/*
 * Normalize truth table tt with three columns
 * - the three labels are literals
 */
void normalize_truth_table3(ttbl_t *tt) {
  literal_t l;
  bvar_t aux;

  assert(tt->nvars == 3);

  // convert literals to variables and negate if required
  l = tt->label[0];
  tt->label[0] = var_of(l);
  if (is_neg(l)) {
    tt->mask = negate0(tt->mask);
  }

  l = tt->label[1];
  tt->label[1] = var_of(l);
  if (is_neg(l)) {
    tt->mask = negate1(tt->mask);
  }

  l = tt->label[2];
  tt->label[2] = var_of(l);
  if (is_neg(l)) {
    tt->mask = negate2(tt->mask);
  }

  // sort columns in non-decreasing order
  if (tt->label[0] > tt->label[1]) {
    aux = tt->label[0];
    tt->label[0] = tt->label[1];
    tt->label[1] = aux;
    tt->mask = swap01(tt->mask);
  }

  if (tt->label[1] > tt->label[2]) {
    aux = tt->label[1];
    tt->label[1] = tt->label[2];
    tt->label[2] = aux;
    tt->mask = swap12(tt->mask);
  }

  if (tt->label[0] > tt->label[1]) {
    aux = tt->label[0];
    tt->label[0] = tt->label[1];
    tt->label[1] = aux;
    tt->mask = swap01(tt->mask);
  }

  assert(0 <= tt->label[0] && tt->label[0] <= tt->label[1] && tt->label[1] <= tt->label[2]);

  // merge equal columns
  if (tt->label[1] == tt->label[2]) {
    tt->nvars --;
    tt->label[2] = null_bvar;
    tt->mask = merge12(tt->mask);
  }

  if (tt->label[0] == tt->label[1]) {
    tt->nvars --;
    tt->label[1] = tt->label[2];
    tt->label[2] = null_bvar;
    tt->mask = merge01(tt->mask);
  }

  // remove column 0 if it's true
  if (tt->label[0] == const_bvar) {
    tt->nvars --;
    tt->label[0] = tt->label[1];
    tt->label[1] = tt->label[2];
    tt->label[2] = null_bvar;
    tt->mask = force_true0(tt->mask);
  }

  // remove irrelevant columns
  if (tt->nvars == 3 && irrelevant2(tt->mask)) {
    tt->nvars --;
    tt->label[2] = null_bvar;
    tt->mask = remove2(tt->mask);
  }

  if (tt->nvars > 1 && irrelevant1(tt->mask)) {
    tt->nvars --;
    tt->label[1] = tt->label[2];
    tt->label[2] = null_bvar;
    tt->mask = remove1(tt->mask);
  }

  if (tt->nvars > 0 && irrelevant0(tt->mask)) {
    tt->nvars --;
    tt->label[0] = tt->label[1];
    tt->label[1] = tt->label[2];
    tt->label[2] = null_bvar;
    tt->mask = remove0(tt->mask);
  }

  assert(normal_truth_table(tt));
}


/*
 * Normalize a truth table with two columns
 * - label[0] and label[1] are literals
 */
void normalize_truth_table2(ttbl_t *tt) {
  literal_t l;
  bvar_t aux;

  assert(tt->nvars == 2 && tt->label[2] == null_bvar && irrelevant2(tt->mask));

  // convert literals to variables and negate if required
  l = tt->label[0];
  tt->label[0] = var_of(l);
  if (is_neg(l)) {
    tt->mask = negate0(tt->mask);
  }

  l = tt->label[1];
  tt->label[1] = var_of(l);
  if (is_neg(l)) {
    tt->mask = negate1(tt->mask);
  }

  // sort
  if (tt->label[0] > tt->label[1]) {
    aux = tt->label[0];
    tt->label[0] = tt->label[1];
    tt->label[1] = aux;
    tt->mask = swap01(tt->mask);
  }

  assert(0 <= tt->label[0] && tt->label[0] <= tt->label[1]);

  // merge columns if equal
  if (tt->label[0] == tt->label[1]) {
    tt->nvars --;
    tt->label[1] = null_bvar;
    tt->mask = merge01(tt->mask);
  }

  // remove column 0 if it's true
  if (tt->label[0] == const_bvar) {
    tt->nvars --;
    tt->label[0] = tt->label[1];
    tt->label[1] = null_bvar;
    tt->mask = force_true0(tt->mask);
  }

  // remove irrelevant columns
  if (tt->nvars == 2 && irrelevant1(tt->mask)) {
    tt->nvars --;
    tt->label[1] = null_bvar;
    tt->mask = remove1(tt->mask); // no change
  }

  if (tt->nvars > 0 && irrelevant0(tt->mask)) {
    tt->nvars --;
    tt->label[0] = tt->label[1];
    tt->label[1] = null_bvar;
    tt->mask = remove0(tt->mask);
  }

  assert(normal_truth_table(tt));
}


/*
 * Normalize a ttbl with one column
 */
static void normalize_truth_table1(ttbl_t *tt) {
  literal_t l;

  assert(tt->nvars == 1 && tt->label[1] == null_bvar && tt->label[2] == null_bvar &&
	 irrelevant1(tt->mask) && irrelevant2(tt->mask));

  l = tt->label[0];
  tt->label[0] = var_of(l);
  if (is_neg(l)) {
    tt->mask = negate0(tt->mask);
  }

  if (irrelevant0(tt->mask)) {
    tt->nvars = 0;
    tt->label[0] = null_bvar;
  }

  assert(normal_truth_table(tt));
}

/*
 * General form: normalize a truth table tt
 */
void normalize_truth_table(ttbl_t *tt) {
  switch (tt->nvars) {
  case 3:
    normalize_truth_table3(tt);
    break;

  case 2:
    normalize_truth_table2(tt);
    break;

  case 1:
    normalize_truth_table1(tt);
    break;

  default:
    // nothing to do
    assert(tt->nvars == 0);
    assert(normal_truth_table(tt));
    break;
  }
}

/*
 * Literal encoded in tt
 * - tt must have a single variable
 */
literal_t literal_of_ttbl1(ttbl_t *tt) {
  bvar_t x;

  assert(normal_truth_table(tt));
  assert(tt->nvars == 1);
  x = tt->label[0];
  return tt->mask == 0xf0 ? pos_lit(x) : neg_lit(x);
}

/*
 * Literal encoded in tt
 * - tt must be a constant function (tt->nvars == 0)
 */
literal_t literal_of_ttbl0(ttbl_t *tt) {
  assert(normal_truth_table(tt));
  assert(tt->nvars == 0);
  return tt->mask == 0x00 ? false_literal : true_literal;
}




/*
 * Check that all elements of array b are either 0 or 1
 */
#ifndef NDEBUG
static bool is_bit_array(const uint8_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (b[i] > 1) return false;
  }
  return true;
}
#endif

/*
 * Pack b[8] into an 8-bit mask (for a ternary ttbl)
 */
static uint8_t pack_ttbl(uint8_t b[8]) {
  assert(is_bit_array(b, 8));
  return b[0] | (b[1] << 1) | (b[2] << 2) | (b[3] << 3) |
    (b[4] << 4) | (b[5] << 5) | (b[6] << 6) | (b[7] << 7);
}


/*
 * Unpack a binary truth-table mask:
 * - the mask must be of the form b0 b0 b1 b1 b2 b2 b3 b3
 * - we store the four bits in b[0..3]
 */
static void unpack_bin_ttbl(uint8_t mask, uint8_t b[4]) {
  assert(irrelevant2(mask));
  b[0] = mask & 1;
  b[1] = (mask >> 2) & 1;
  b[2] = (mask >> 4) & 1;
  b[3] = (mask >> 6) & 1;

  assert(is_bit_array(b, 4));
}


/*
 * Unpack a ternary truth-table mask b0 b1 b2 b3 b4 b5 b6 b7
 * - store bit i into b[i]
 */
static void unpack_ternary_ttbl(uint8_t mask, uint8_t b[8]) {
  uint32_t i;

  for (i=0; i<8; i++) {
    b[i] = mask & 1;
    mask >>= 1;
  }

  assert(is_bit_array(b, 8));
}


/*
 * Combine two binary truth tables:
 * - tt1 defines a function f(x, y)
 * - tt2 defines x as a function g(z, t)
 * - the result is the truth table for f(g(z, t), y)
 */
void compose_ttbl_left(const ttbl_t *tt1, const ttbl_t *tt2, ttbl_t *result) {
  uint8_t f[4];
  uint8_t g[4];
  uint8_t r[8];

  assert(tt1->nvars == 2 && tt2->nvars == 2);

  unpack_bin_ttbl(tt1->mask, f);
  unpack_bin_ttbl(tt2->mask, g);

  // result table
  r[0] = f[2 * g[0]];      // f(g(0, 0), 0)
  r[1] = f[2 * g[0] + 1];  // f(g(0, 0), 1)
  r[2] = f[2 * g[1]];      // f(g(0, 1), 0)
  r[3] = f[2 * g[1] + 1];  // f(g(0, 1), 1)
  r[4] = f[2 * g[2]];      // f(g(1, 0), 0)
  r[5] = f[2 * g[2] + 1];  // f(g(1, 0), 1)
  r[6] = f[2 * g[3]];      // f(g(1, 1), 0)
  r[7] = f[2 * g[3] + 1];  // f(g(1, 1), 1)

  result->nvars = 3;
  result->label[0] = pos_lit(tt2->label[0]); // z
  result->label[1] = pos_lit(tt2->label[1]); // t
  result->label[2] = pos_lit(tt1->label[1]); // y
  result->mask = pack_ttbl(r);

  normalize_truth_table3(result);
}


/*
 * Combine two truth tables:
 * - tt1 defines f(x, y)
 * - tt2 defines y as a g(z, t)
 * - the result is the truth table for f(x, g(z, t))
 */
void compose_ttbl_right(const ttbl_t *tt1, const ttbl_t *tt2, ttbl_t *result) {
  uint8_t f[4];
  uint8_t g[4];
  uint8_t r[8];

  assert(tt1->nvars == 2 && tt2->nvars == 2);

  unpack_bin_ttbl(tt1->mask, f);
  unpack_bin_ttbl(tt2->mask, g);

  // result table
  r[0] = f[g[0]];          // f(0, g(0, 0))
  r[1] = f[g[1]];          // f(0, g(0, 1))
  r[2] = f[g[2]];          // f(0, g(1, 0))
  r[3] = f[g[3]];          // f(0, g(1, 1))
  r[4] = f[2 + g[0]];      // f(1, g(0, 0))
  r[5] = f[2 + g[1]];      // f(1, g(0, 1))
  r[6] = f[2 + g[2]];      // f(1, g(1, 0))
  r[7] = f[2 + g[3]];      // f(1, g(1, 1))

  result->nvars = 3;
  result->label[0] = pos_lit(tt1->label[0]); // x
  result->label[1] = pos_lit(tt2->label[0]); // z
  result->label[2] = pos_lit(tt2->label[1]); // t
  result->mask = pack_ttbl(r);

  normalize_truth_table3(result);
}


/*
 * Compose three truth tables:
 * - tt1 = f(x, y)
 * - tt2 = g(a, b) for x
 * - tt3 = h(c, d) for y
 * - stores the unpacked truth table for f(g(a, b), h(c, d)) in r[0 .. 15]
 */
static void expand_ttbl(const ttbl_t *tt1, const ttbl_t *tt2, const ttbl_t *tt3, uint8_t r[16]) {
  uint8_t f[4], g[4], h[4];

  assert(tt1->nvars == 2 && tt2->nvars == 2 && tt3->nvars == 2);

  unpack_bin_ttbl(tt1->mask, f);
  unpack_bin_ttbl(tt2->mask, g);
  unpack_bin_ttbl(tt3->mask, h);

  r[0]  = f[2 * g[0] + h[0]];  // f(g(0, 0), h(0, 0))
  r[1]  = f[2 * g[0] + h[1]];  // f(g(0, 0), h(0, 1))
  r[2]  = f[2 * g[0] + h[2]];  // f(g(0, 0), h(1, 0))
  r[3]  = f[2 * g[0] + h[3]];  // f(g(0, 0), h(1, 1))
  r[4]  = f[2 * g[1] + h[0]];  // f(g(0, 1), h(0, 0))
  r[5]  = f[2 * g[1] + h[1]];  // f(g(0, 1), h(0, 1))
  r[6]  = f[2 * g[1] + h[2]];  // f(g(0, 1), h(1, 0))
  r[7]  = f[2 * g[1] + h[3]];  // f(g(0, 1), h(1, 1))
  r[8]  = f[2 * g[2] + h[0]];  // f(g(1, 0), h(0, 0))
  r[9]  = f[2 * g[2] + h[1]];  // f(g(1, 0), h(0, 1))
  r[10] = f[2 * g[2] + h[2]];  // f(g(1, 0), h(1, 0))
  r[11] = f[2 * g[2] + h[3]];  // f(g(1, 0), h(1, 1))
  r[12] = f[2 * g[3] + h[0]];  // f(g(1, 1), h(0, 0))
  r[13] = f[2 * g[3] + h[1]];  // f(g(1, 1), h(0, 1))
  r[14] = f[2 * g[3] + h[2]];  // f(g(1, 1), h(1, 0))
  r[15] = f[2 * g[3] + h[3]];  // f(g(1, 1), h(1, 1))
}

/*
 * Merge two columns in a 4-variable truth table
 * - f[0 .. 15] = truth table
 * - i and j = the two columns to merge
 *   i and j must be distinct and between 0 and 3
 * - r[0 .. 7] = result table
 *
 * There are six merge operations, each maps some index k between 0
 * and 7 to an index between 0 and 15. The mapping is defined by
 * writing k in binary then replacing the missing binary digit.
 *
 * For example, if we merge column 0 and 2:
 *   k in binary is b0 b1 b2, it's mapped to b0 b1 b0 b2
 *   (e.g., 010 --> 0100 so 2 --> 4)
 * The full map is then
 *   0 --> 0
 *   1 --> 1
 *   2 --> 4
 *   3 --> 5
 *   4 --> 10
 *   5 --> 11
 *   6 --> 14
 *   7 --> 15
 *
 * We store the six maps corresponding to these six merge operations
 * in array merge[6][8].
 */
static const uint8_t merge[6][8] = {
  { 0, 1, 2, 3, 12, 13, 14, 15 },  // merge columns 0 and 1
  { 0, 1, 4, 5, 10, 11, 14, 15 },  // merge columns 0 and 2
  { 0, 2, 4, 6,  9, 11, 13, 15 },  // merge columns 0 and 3
  { 0, 1, 6, 7,  8,  9, 14, 15 },  // merge columns 1 and 2
  { 0, 2, 5, 7,  8, 10, 13, 15 },  // merge columns 1 and 3
  { 0, 3, 4, 7,  8, 11, 12, 15 },  // merge columns 2 and 3
};

// merge_idx[i][j] = k if merge[k] merges column i and j
static const uint8_t merge_idx[4][4] = {
  { 100, 0, 1, 2 },
  { 0, 100, 3, 4 },
  { 1, 3, 100, 5 },
  { 2, 4, 5, 100 },
};

static void merge_columns(const uint8_t f[16], uint32_t i, uint32_t j, uint8_t r[8]) {
  uint32_t k, t;

  assert(i != j && i <= 3 && j <= 3);
  assert(is_bit_array(f, 16));

  k = merge_idx[i][j];

  assert(k <= 5);

  for (t=0; t<8; t++) {
    r[t] = f[merge[k][t]];
  }

  assert(is_bit_array(r, 8));
}


/*
 * Try to compose three tables and reduce the result to
 * a three column table.
 * - tt1 defines f(x, y)
 * - tt2 defines g(a, b) for x
 * - tt3 defined h(c, d) for y
 *
 * The function returns true if at least two of the
 * variables a, b, c, d are equal and store the truth-table
 * for f(g(a, b), h(c, d)) into result.
 *
 * The function returns false otherwise.
 */
bool compose_ttbl_left_right1(const ttbl_t *tt1, const ttbl_t *tt2, const ttbl_t *tt3, ttbl_t *result) {
  uint8_t aux[16];
  uint8_t r[8];
  int32_t v[4];  // four variables of tt2 and tt3
  uint32_t i, j; // two columns with the same variables
  uint32_t k;

  assert(tt1->nvars == 2 && tt2->nvars == 2 && tt3->nvars == 2);

  v[0] = tt2->label[0];
  v[1] = tt2->label[1];
  v[2] = tt3->label[0];
  v[3] = tt3->label[1];

  for (i=0; i<3; i++) {
    for (j=i+1; j<4; j++) {
      if (v[i] == v[j]) goto found;
    }
  }
  return false;

 found:
  assert(i < j && v[i] == v[j]);

  expand_ttbl(tt1, tt2, tt3, aux);
  merge_columns(aux, i, j, r);

  result->nvars = 3;
  k = 0;
  for (i=0; i<4; i++) {
    if (i == j) continue;
    result->label[k] = pos_lit(v[i]);
    k ++;
  }
  result->mask = pack_ttbl(r);

  normalize_truth_table3(result);

  return true;
}


/*
 * Check whether the two variables of tt1 are also variables ot tt2
 * - tt2  must be a table with three columns
 * - both tt1 and tt2 must be normalized (so tt1->label[0] < tt1->label[1]
 *   and tt2->label[0] < tt2->label[1] < tt2->label[2]).
 * - return an index k between 0 and 2 if so
 * - return 3 otherwise.
 *
 * The index k is the missing column: tt2->label[k] is the variable
 * or tt2 that's not equal to tt1->label[0] or tt1->label[1].
 */
static uint32_t match_two_to_three_vars(const ttbl_t *tt1, const ttbl_t *tt2) {
  assert(tt1->nvars == 2 && tt2->nvars == 3);
  assert(normal_truth_table(tt1));
  assert(normal_truth_table(tt2));

  if (tt1->label[0] == tt2->label[0] && tt1->label[1] == tt2->label[1]) {
    return 2;
  }

  if (tt1->label[0] == tt2->label[0] && tt1->label[1] == tt2->label[2]) {
    return 1;
  }

  if (tt1->label[0] == tt2->label[1] && tt1->label[1] == tt2->label[2]) {
    return 0;
  }

  return 3;
}


/*
 * Extend a two-column truth table to three columns:
 * - f[0 .. 3]: input table
 * - i = index of the missing column: i must be between 0 and 2
 * - r[0 ... 7]: output = f extended to 3 columns
 *
 * There are three extension maps depending on i
 * - for j=0 to 7, we set  r[j] = f[extend[i][j]]
 */
static const uint8_t extend[3][8] = {
  { 0, 1, 2, 3, 0, 1, 2, 3 }, // add column 0
  { 0, 1, 0, 1, 2, 3, 2, 3 }, // add column 1
  { 0, 0, 1, 1, 2, 2, 3, 3 }, // add column 2
};

static void add_column(const uint8_t f[4], uint32_t i, uint8_t r[8]) {
  uint32_t j;

  assert(is_bit_array(f, 4));
  assert(i <= 2);

  for (j=0; j<8; j++) {
    r[j] = f[extend[i][j]];
  }

  assert(is_bit_array(r, 8));
}

/*
 * Build the truth table r for f(g(a, b, c), h(a, b, c))
 */
static void compose_ttbls(const uint8_t f[4], const uint8_t g[8], const uint8_t h[8], uint8_t r[8]) {
  assert(is_bit_array(f, 4) && is_bit_array(g, 8) && is_bit_array(h, 8));

  r[0] = f[2 * g[0] + h[0]]; // f(g(0, 0, 0), h(0, 0, 0))
  r[1] = f[2 * g[1] + h[1]]; // f(g(0, 0, 1), h(0, 0, 1))
  r[2] = f[2 * g[2] + h[2]]; // f(g(0, 1, 0), h(0, 1, 0))
  r[3] = f[2 * g[3] + h[3]]; // f(g(0, 1, 1), h(0, 1, 1))
  r[4] = f[2 * g[4] + h[4]]; // f(g(1, 0, 0), h(1, 0, 0))
  r[5] = f[2 * g[5] + h[5]]; // f(g(1, 0, 1), h(1, 0, 1))
  r[6] = f[2 * g[6] + h[6]]; // f(g(1, 1, 0), h(1, 1, 0))
  r[7] = f[2 * g[7] + h[7]]; // f(g(1, 1, 1), h(1, 1, 1))

  assert(is_bit_array(r, 8));
}


/*
 * Try to compose three tables and reduce the result to a three-column table.
 * - tt1 defines f(x, y)
 * - tt2 defines g(a, b) for x
 * - tt3 defines h(c, d, e) for y
 *
 * Succeed if { a, b } is a subset of { c, d, e }.
 * In this case, store the truth table for f(g(a, b), h(c, d, e)) in result.
 * Otherwise return false.
 */
bool compose_ttbl_left_right2(const ttbl_t *tt1, const ttbl_t *tt2, const ttbl_t *tt3, ttbl_t *result) {
  uint8_t f[4];
  uint8_t g[4];
  uint8_t full_g[8];
  uint8_t h[8];
  uint8_t r[8];
  uint32_t k;

  assert(tt1->nvars == 2 && tt2->nvars == 2 && tt3->nvars == 3);

  k = match_two_to_three_vars(tt2, tt3);
  if (k > 2) return false;

  unpack_bin_ttbl(tt1->mask, f);
  unpack_bin_ttbl(tt2->mask, g);
  add_column(g, k, full_g);
  unpack_ternary_ttbl(tt3->mask, h);
  compose_ttbls(f, full_g, h, r);

  result->nvars = 3;
  result->label[0] = pos_lit(tt3->label[0]);
  result->label[1] = pos_lit(tt3->label[1]);
  result->label[2] = pos_lit(tt3->label[2]);
  result->mask = pack_ttbl(r);

  normalize_truth_table3(result);

  return true;
}

/*
 * Same thing but with the tt2 defining a ternary function and tt3 a binary function.
 * - tt1 defines f(x, y)
 * - tt2 defines g(a, b, c) for x
 * - tt3 defiens h(e, f) for y
 *
 * Succeed if { e, f } is a subset of { a, b, c}.
 * Return true and store the table for f(g(a, b, c), h(e, f)) in result.
 * Otherwise, return false.
 */
bool compose_ttbl_left_right3(const ttbl_t *tt1, const ttbl_t *tt2, const ttbl_t *tt3, ttbl_t *result) {
  uint8_t f[4];
  uint8_t g[8];
  uint8_t h[4];
  uint8_t full_h[8];
  uint8_t r[8];
  uint32_t k;

  assert(tt1->nvars == 2 && tt2->nvars == 3 && tt3->nvars == 2);

  k = match_two_to_three_vars(tt3, tt2);
  if (k > 2) return false;

  unpack_bin_ttbl(tt1->mask, f);
  unpack_ternary_ttbl(tt2->mask, g);
  unpack_bin_ttbl(tt3->mask, h);
  add_column(h, k, full_h);
  compose_ttbls(f, g, full_h, r);

  result->nvars = 3;
  result->label[0] = pos_lit(tt2->label[0]);
  result->label[1] = pos_lit(tt2->label[1]);
  result->label[2] = pos_lit(tt2->label[2]);
  result->mask = pack_ttbl(r);

  normalize_truth_table3(result);

  return true;
}


/*
 * Same thing but with two ternary functions:
 * - tt1 defines f(x, y)
 * - tt2 defines g(a, b, c) for x
 * - tt3 defines h(d, e, f) for y
 *
 * Succeed if a = d and b = e and c = f.
 * Then store the table for f(g(a, b, c), h(d, e, f)) in result.
 * Otherwise return false.
 */
bool compose_ttbl_left_right4(const ttbl_t *tt1, const ttbl_t *tt2, const ttbl_t *tt3, ttbl_t *result) {
  uint8_t f[4];
  uint8_t g[8];
  uint8_t h[8];
  uint8_t r[8];

  assert(tt1->nvars == 2 && tt2->nvars == 3 && tt3->nvars == 3);

  if (tt2->label[0] == tt3->label[0] && tt2->label[1] == tt3->label[1]
      && tt2->label[2] == tt3->label[2]) {
    unpack_bin_ttbl(tt1->mask, f);
    unpack_ternary_ttbl(tt2->mask, g);
    unpack_ternary_ttbl(tt3->mask, h);
    compose_ttbls(f, g, h, r);

    result->nvars = 3;
    result->label[0] = pos_lit(tt2->label[0]);
    result->label[1] = pos_lit(tt2->label[1]);
    result->label[2] = pos_lit(tt2->label[2]);
    result->mask = pack_ttbl(r);

    normalize_truth_table3(result);

    return true;
  }

  return false;
}


/*
 * General form:
 * - tt1 defines f(x, y)
 * - tt2 defines a function g(...) for x (either binary or ternary)
 * - tt3 defines a function h(...) for y (either binary or ternary)
 *
 * Succeed if f(g(...), h(...)) can be reduced to a three-column table.
 * Store the result in *result if so, and return true.
 * Return false otherwise.
 */
bool compose_ttbl_left_right(const ttbl_t *tt1, const ttbl_t *tt2, const ttbl_t *tt3, ttbl_t *result) {
  assert(tt1->nvars == 2 && tt2->nvars >= 2 && tt3->nvars >= 2);

  if (tt2->nvars == 2) {
    if (tt3->nvars == 2) {
      return compose_ttbl_left_right1(tt1, tt2, tt3, result);
    } else {
      return compose_ttbl_left_right2(tt1, tt2, tt3, result);
    }
  } else {
    if (tt3->nvars == 2) {
      return compose_ttbl_left_right3(tt1, tt2, tt3, result);
    } else {
      return compose_ttbl_left_right4(tt1, tt2, tt3, result);
    }
  }
}

