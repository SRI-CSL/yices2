/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
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
 * EXPERIMENTAL: BOOLEAN GATES
 */
#include <assert.h>

#include "solvers/cdcl/new_gates.h"
#include "utils/memalloc.h"


/*
 * ARRAY OF GATE DESCRIPTORS
 */
void init_bgate_array(bgate_array_t *a) {
  a->data = NULL;
  a->ngates = 0;
  a->size = 0;
}

static void extend_bgate_array(bgate_array_t *a) {
  uint32_t n;

  n = a->size;
  if (n == 0) {
    n = DEF_BGATE_ARRAY_SIZE; // first allocation
    assert(n <= MAX_BGATE_ARRAY_SIZE);
    a->data = (bgate_t *) safe_malloc(n * sizeof(bgate_t));
    a->size = n;
  } else {
    // try to make the table 50% larger
    n += (n >> 1);
    assert(n > a->size);
    if (n > MAX_BGATE_ARRAY_SIZE) {
      out_of_memory();
    }

    a->data = (bgate_t *) safe_realloc(a->data, n * sizeof(bgate_t));
    a->size = n;
  }
}

void delete_bgate_array(bgate_array_t *a) {
  safe_free(a->data);
  a->data = NULL;
}


/*
 * Store a new descriptor in a
 * - tt = (normalized) truth table
 * - return the index of the newly allocated element
 */
uint32_t store_bgate(bgate_array_t *a, ttbl_t *tt) {
  uint32_t i;

  i = a->ngates;
  if (i == a->size) {
    extend_bgate_array(a);
  }
  assert(i < a->size);
  a->data[i].ttbl = tt->mask;
  a->data[i].var[0] = tt->label[0];
  a->data[i].var[1] = tt->label[1];
  a->data[i].var[2] = tt->label[2];
  a->ngates = i+1;

  return i;
}


/*
 * Arity = number of non-null variables in g
 */
static uint32_t bgate_arity(bgate_t *g) {
  uint32_t n;

  n = (g->var[0] >= 0) + (g->var[1] >= 0) + (g->var[2] >= 2);
  assert(n <= 3);
  return n;
}


/*
 * Get the truth table for gate i: store it in tt
 */
void get_bgate(const bgate_array_t *a, uint32_t i, ttbl_t *tt) {
  assert(i < a->size);
  assert(a->data[i].ttbl < 256);

  tt->nvars = bgate_arity(a->data + i);
  tt->label[0] = a->data[i].var[0];
  tt->label[1] = a->data[i].var[1];
  tt->label[2] = a->data[i].var[2];
  tt->mask = a->data[i].ttbl;
}



/*
 * Normalize and store a gate with two input literals.
 * - b = truth table for the gate
 *   (only the eight low-order bits are used)
 * - l1, l2 = input literals
 * 
 * - b must be of the form [b3 b3 b2 b2 b1 b1 b0 b0]
 * - this defines a function f(l1, l2) with the following table
 *     
 *     l1   l2    f
 *
 *      0    0    b0
 *      0    1    b1
 *      1    0    b2
 *      1    1    b3
 */
uint32_t store_binary_gate(bgate_array_t *a, uint32_t b, literal_t l1, literal_t l2) {
  ttbl_t tt;

  tt.nvars = 2;
  tt.label[0] = l1;
  tt.label[1] = l2;
  tt.label[2] = null_bvar;
  tt.mask = (uint8_t) b;
  normalize_truth_table2(&tt);

  return store_bgate(a, &tt);  
}

 
/*
 * Normalize and store a gate with three input literals:
 * - b = truth table for the gate
 *   (only the eight low-order bits are used)
 * - l1, l2, l3 = input literals
 *
 * - b is [b7 b6 b5 b4 b3 b2 b1 b0]
 * - the corresponding function is defined by this table:
 *
 *   l1   l2   l3    f 
 *
 *    0    0    0    b0
 *    0    0    1    b1
 *    0    1    0    b2
 *    0    1    1    b3
 *    1    0    0    b4
 *    1    0    1    b5
 *    1    1    0    b6
 *    1    1    1    b7
 */
uint32_t store_ternary_gate(bgate_array_t *a, uint32_t b, literal_t l1, literal_t l2, literal_t l3) {
  ttbl_t tt;

  tt.nvars = 3;
  tt.label[0] = l1;
  tt.label[1] = l2;
  tt.label[2] = l3;
  tt.mask = (uint8_t) b;
  normalize_truth_table3(&tt);

  return store_bgate(a, &tt);
}
