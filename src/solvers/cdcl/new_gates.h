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

#ifndef __NEW_GATES_H
#define __NEW_GATES_H

#include <stdint.h>

#include "solvers/cdcl/truth_tables.h"

/*
 * Truth tables for Boolean gates of arity <= 3
 *
 * - for functions of arity 3,
 *     var[0], var[1], var[2] are the indices of three Boolean variables
 *     in increasing order
 * - for functions of arity 2, var[2] is not used (it's null_bvar = -1)
 *     var[0] and var[1] are two Boolean variables
 *
 * - the truth table is an array of 8bits b7 ... b0
 * - the encoding is as follows
 *
 *    var[0] var[1] var[2]  f
 *       0      0      0    b0
 *       0      0      1    b1
 *       0      1      0    b2
 *       0      1      1    b3
 *       1      0      0    b4
 *       1      0      1    b5
 *       1      1      0    b6
 *       1      1      1    b7
 *
 * For functions of arity 2, this looks like:
 *
 *    var[0] var[1] var[2]  f
 *       0      0      0    b0
 *       0      0      1    b0
 *       0      1      0    b2
 *       0      1      1    b2
 *       1      0      0    b4
 *       1      0      1    b4
 *       1      1      0    b6
 *       1      1      1    b6
 *
 * and var[2] is set to -1.
 */
typedef struct bgate_s {
  uint32_t ttbl;  // truth table: only 8bits are used
  bvar_t  var[3]; // variables in increasing order
} bgate_t;



/*
 * Resizable array of bgate_t descriptors
 * - size = size of array data
 * - ngates = total number of gates in use
 */
typedef struct bgate_array_s {
  bgate_t *data;
  uint32_t ngates;
  uint32_t size;
} bgate_array_t;

#define DEF_BGATE_ARRAY_SIZE 1024
#define MAX_BGATE_ARRAY_SIZE (UINT32_MAX/sizeof(bgate_t))


/*
 * Initialization: nothing allocated yet
 */
extern void init_bgate_array(bgate_array_t *a);

/*
 * Free memory
 */
extern void delete_bgate_array(bgate_array_t *a);

/*
 * Empty the table
 */
static inline void reset_bgate_array(bgate_array_t *a) {
  a->ngates = 0;
}

/*
 * Store a new descriptor in a
 * - tt = (normalized) truth table
 * - return the index of the newly allocated element
 */
extern uint32_t store_bgate(bgate_array_t *a, ttbl_t *tt);



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
extern uint32_t store_binary_gate(bgate_array_t *a, uint32_t b, literal_t l1, literal_t l2);

 
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
extern uint32_t store_ternary_gate(bgate_array_t *a, uint32_t b, literal_t l1, literal_t l2, literal_t l3);


/*
 * Common binary gates
 */
static inline uint32_t store_or2(bgate_array_t *a, literal_t l1, literal_t l2) {
  return store_binary_gate(a, 0xfc, l1, l2);
}

static inline uint32_t store_and2(bgate_array_t *a, literal_t l1, literal_t l2) {
  return store_binary_gate(a, 0xc0, l1, l2);
}

static inline uint32_t store_xor2(bgate_array_t *a, literal_t l1, literal_t l2) {
  return store_binary_gate(a, 0x3c, l1, l2);
}


/*
 * Common ternary gates
 */
static inline literal_t store_or3(bgate_array_t *a, literal_t l1, literal_t l2, literal_t l3) {
  return store_ternary_gate(a, 0xfe, l1, l2, l3);
}

static inline literal_t store_xor3(bgate_array_t *a, literal_t l1, literal_t l2, literal_t l3) {
  return store_ternary_gate(a, 0x96, l1, l2, l3);
}

static inline literal_t store_maj3(bgate_array_t *a, literal_t l1, literal_t l2, literal_t l3) {
  return store_ternary_gate(a, 0xe8, l1, l2, l3);
}

static inline literal_t store_ite(bgate_array_t *a, literal_t c, literal_t l1, literal_t l2) {
  return store_ternary_gate(a, 0xca, c, l1, l2);
}

/*
 * Get the truth table for gate i: store it in tt
 */
extern void get_bgate(const bgate_array_t *a, uint32_t i, ttbl_t *tt);

/*
 * Get i-th element in the array
 */
static inline bgate_t *bgate(const bgate_array_t *a, uint32_t i) {
  assert(i < a->size);
  return a->data + i;
}


#endif /* __NEW_GATES_H */
