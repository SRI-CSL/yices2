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
 * EXPERIMENTAL: SUPPORT TO DETECT EQUIVALENCE BETWEEN GATES
 */

#include <assert.h>

#include "solvers/cdcl/gate_equiv.h"


/*
 * ARRAY OF GATE DESCRIPTORS
 */
static void init_bgate_array(bgate_array_t *a) {
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

static void delete_bgate_array(bgate_array_t *a) {
  safe_free(a->data);
  a->data = NULL;
}


/*
 * Store a new descriptor in a
 * - tt = (normalized) truth table
 * - return the index of the newly allocated element
 */
static uint32_t store_bgate(bgate_array_t *a, ttbl_t *tt) {
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
 * ARRAY OF VARIABLE DEFINITIONS
 */
static void init_bdef_array(bdef_array_t *a) {
  a->data = NULL;
  a->ndefs = 0;
  a->size = 0;
}

static void extend_bdef_array(bdef_array_t *a) {
  uint32_t n;

  n = a->size;
  if (n == 0) {
    n = DEF_BDEF_ARRAY_SIZE; // first allocation
    assert(n <= MAX_BDEF_ARRAY_SIZE);
    a->data = (bvar_def_t *) safe_malloc(n * sizeof(bvar_def_t));
    a->size = n;
  } else {
    // try to make the table 50% larger
    n += (n >> 1);
    assert(n > a->size);
    if (n > MAX_BDEF_ARRAY_SIZE) {
      out_of_memory();
    }

    a->data = (bvar_def_t *) safe_realloc(a->data, n * sizeof(bvar_def_t));
    a->size = n;
  }
}

static void delete_bdef_array(bdef_array_t *a) {
  safe_free(a->data);
  a->data = NULL;
}


/*
 * Add pair (var, gate) at the end of array a
 */
static void bdef_array_add(bdef_array_t *a, bvar_t var, uint32_t gate) {
  uint32_t i;

  i = a->ndefs;
  if (i == a->size) {
    extend_bdef_array(a);
  }
  assert(i < a->size);
  a->data[i].var = var;
  a->data[i].gate = gate;
  a->ndefs = i+1;
}


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
static bool normal_truth_table(ttbl_t *tt) {
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
static void normalize_truth_table3(ttbl_t *tt) {
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
static void normalize_truth_table2(ttbl_t *tt) {
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
 * FULL TABLE
 */

/*
 * Initialization
 */
void init_bdef_table(bdef_table_t *table, void *sat_solver, base_lit_fun_t b) {
  table->sat_solver = sat_solver;
  table->base_lit = b;
  init_bgate_array(&table->gates);
  init_bdef_array(&table->defs);
}

/*
 * Deletion
 */
void delete_bdef_table(bdef_table_t *table) {
  delete_bgate_array(&table->gates);
  delete_bdef_array(&table->defs);
}


/*
 * Add a definition:
 * - v = variable
 * - ttbl = truth table defining v (must be normalized)
 */
static void add_bvar_def(bdef_table_t *table, bvar_t v, ttbl_t *tt) {
  uint32_t i;

  assert(normal_truth_table(tt));
  
  i = store_bgate(&table->gates, tt);
  bdef_array_add(&table->defs, v, i);
}


/*
 * Get the base literal for l
 */
static inline literal_t base_lit(bdef_table_t *table, literal_t l) {
  return table->base_lit(table->sat_solver, l);
}

/*
 * Process a binary gate definition
 * - b = truth table for the gate opertator.
 *   only the lower 8 btis are used.
 *   b must be of the form [b3 b3 b2 b2 b1 b1 b0 b0]
 * - l = gate output
 * - a1, a2 = two input literals
 */
static void add_binary_gate(bdef_table_t *table, uint32_t b, literal_t l, literal_t a1, literal_t a2) {
  ttbl_t tt;

  // l can be true_literal or false_literal, in which case we skip this gate
  l = base_lit(table, l);
  if (var_of(l) != const_bvar) {
    tt.nvars = 2;
    tt.label[0] = base_lit(table, a1);
    tt.label[1] = base_lit(table, a2);
    tt.label[2] = null_bvar;
    tt.mask = (uint8_t) b;
    normalize_truth_table2(&tt);
    
    if (is_neg(l)) {
      tt.mask = ~tt.mask;    
    }

    add_bvar_def(table, var_of(l), &tt);
  }
}


/*
 * Process a ternary gate
 * - b = truth table for the operator (only 8 lower-order bits are used)
 * - l = gate output
 * - a1, a2, a3 = gate input
 */
static void add_ternary_gate(bdef_table_t *table, uint32_t b, literal_t l, literal_t a1, literal_t a2, literal_t a3) {
  ttbl_t tt;

  // l can be true_literal or false_literal, in which case we skip this gate
  l = base_lit(table, l);
  if (var_of(l) != const_bvar) {
    tt.nvars = 3;
    tt.label[0] = base_lit(table, a1);
    tt.label[1] = base_lit(table, a2);
    tt.label[2] = base_lit(table, a3);
    tt.mask = (uint8_t) b;
    normalize_truth_table3(&tt);

    if (is_neg(l)) {
      tt.mask = ~tt.mask;
    }

    add_bvar_def(table, var_of(l), &tt);
  }
}



/*
 * Process a gate descriptor d
 * - if d's arity is <= 3, this adds entry in the table for every
 *   output variable of d.
 */
void bdef_table_process_gate(bdef_table_t *table, const boolgate_t *d) {
  uint32_t n;

  switch (tag_combinator(d->tag)) {
  case XOR_GATE:
    assert(tag_outdegree(d->tag) == 1);
    n = tag_indegree(d->tag);
    if (n == 2) {
      // output is d->lit[2], inputs are d->lit[0] and d->lit[1]
      add_binary_gate(table, 0x3c, d->lit[2], d->lit[0], d->lit[1]);
    } else if (n == 3) {
      // output is d->lit[3], inputs are d->lit[0 .. 2]
      add_ternary_gate(table, 0x96, d->lit[3], d->lit[0], d->lit[1], d->lit[2]);
    }
    break;

  case OR_GATE:
    assert(tag_outdegree(d->tag) == 1);
    n = tag_indegree(d->tag);
    if (n == 2) {
      // output is d->lit[2], inputs are d->lit[0] and d->lit[1]
      add_binary_gate(table, 0xfc, d->lit[2], d->lit[0], d->lit[1]);
    } else if (n == 3) {
      // output is d->lit[3], inputs are d->lit[0 .. 2]
      add_ternary_gate(table, 0xfe, d->lit[3], d->lit[0], d->lit[1], d->lit[2]);
    }
    break;
    
  case ITE_GATE:
    assert(tag_indegree(d->tag) == 3 && tag_outdegree(d->tag) == 1);
    add_ternary_gate(table, 0xca, d->lit[3], d->lit[0], d->lit[1], d->lit[2]);
    break;

  case CMP_GATE:
    assert(tag_indegree(d->tag) == 3 && tag_outdegree(d->tag) == 1);
    add_ternary_gate(table, 0xb2, d->lit[3], d->lit[0], d->lit[1], d->lit[2]);
    break;
    
  case HALFADD_GATE:
    assert(tag_indegree(d->tag) == 2 && tag_outdegree(d->tag) == 2);
    // d->lit[2] = (xor d->lit[0] d->lit[1])
    // d->lit[3] = (and d->lit[0] d->lit[1])
    add_binary_gate(table, 0x3c, d->lit[2], d->lit[0], d->lit[1]);
    add_binary_gate(table, 0xc0, d->lit[3], d->lit[0], d->lit[1]);
    break;
    
  case FULLADD_GATE:
    // d->lit[3] = (xor d->lit[0] d->lit[1] d->lit[2])
    // d->lit[4] = (maj d->lit[0] d->lit[1] d->lit[2])
    assert(tag_indegree(d->tag) == 3 && tag_outdegree(d->tag) == 2);
    add_ternary_gate(table, 0x96, d->lit[3], d->lit[0], d->lit[1], d->lit[2]);
    add_ternary_gate(table, 0xe8, d->lit[4], d->lit[0], d->lit[1], d->lit[2]);
    break;
  }
}


/*
 * Process all gates in gate_table
 */
void bdef_table_process_all_gates(bdef_table_t *table, const gate_table_t *gate_table) {
  uint32_t scan_index;
  boolgate_t *g;

  scan_index = 0;
  g = gate_table_next(gate_table, &scan_index);
  while (g != NULL) {
    bdef_table_process_gate(table, g);
    g = gate_table_next(gate_table, &scan_index);
  }
}

