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

/*
 * HASH TABLE FOR BOOLEAN GATES (ANOTHER ONE)
 */

#ifndef __NEW_GATE_HASH_MAP2_H
#define __NEW_GATE_HASH_MAP2_H

#include <stdint.h>

#include "solvers/cdcl/new_gates.h"
#include "solvers/cdcl/wide_truth_tables.h"

/*
 * Keys are arrays of at most four Boolean variables var[0 .. 3].
 * Each key is mapped to a vector of pairs <truth-table, literal>
 *
 * We use the same conventions as in truth_tables.h and new_gates.h,
 * except that we can have one more variable:
 *
 * Variable/key normalization
 * --------------------------
 * For functions of arity 4: 0 <= var[0] < var[1] < var[2] < var[3]
 * For functions of arity 3: 0 <= var[0] < var[1] < var[2] and var[3] = null_bvar
 * For functions of arity 2: 0 <= var[0] < var[1] and var[2] = var[3] = null_bvar
 *
 * For functions of arity 1: 0 <= var[0] and var[1] = var[2] = var[3] = null_bvar
 * Constant functions: var[0] = var[1] = var[2] = var[3] = null_bvar
 *
 * Truth table stored in 16bits
 * ----------------------------
 * The truth table encodes f(var[0] ... var[3]) using 16 bits:
 * - f(x0, x1, x2, x3) is stored in the i-th bit where i = 8*x0 + 4*x1 + 2*x2 + x3
 *   b0 = low order bit, ...., b15 = high-order bit
 *
 * For functions of arity 4, this looks like this
 *
 *   var[0] var[1] var[2] var[3]   f
 *     0      0      0      0      b0
 *     0      0      0      1      b1
 *     0      0      1      0      b2
 *     0      0      1      1      b3
 *     0      1      0      0      b4
 *     0      1      0      1      b5
 *     0      1      1      0      b6
 *     0      1      1      1      b7
 *     1      0      0      0      b8
 *     1      0      0      1      b9
 *     1      0      1      0      b10
 *     1      0      1      1      b11
 *     1      1      0      0      b12
 *     1      1      0      1      b13
 *     1      1      1      0      b14
 *     1      1      1      1      b15
 *
 * For functions of arity 3, var[3] is ignored:
 *
 *   var[0] var[1] var[2] var[3]   f
 *     0      0      0      0      b0
 *     0      0      0      1      b0
 *     0      0      1      0      b1
 *     0      0      1      1      b1
 *     0      1      0      0      b2
 *     0      1      0      1      b2
 *     0      1      1      0      b3
 *     0      1      1      1      b3
 *     1      0      0      0      b4
 *     1      0      0      1      b4
 *     1      0      1      0      b5
 *     1      0      1      1      b5
 *     1      1      0      0      b6
 *     1      1      0      1      b6
 *     1      1      1      0      b7
 *     1      1      1      1      b7
 *
 * For functions of arity 2, var[2] and var[3] are ignored:
 *
 *   var[0] var[1] var[2] var[3]   f
 *     0      0      0      0      b0
 *     0      0      0      1      b0
 *     0      0      1      0      b0
 *     0      0      1      1      b0
 *     0      1      0      0      b1
 *     0      1      0      1      b1
 *     0      1      1      0      b1
 *     0      1      1      1      b1
 *     1      0      0      0      b2
 *     1      0      0      1      b2
 *     1      0      1      0      b2
 *     1      0      1      1      b2
 *     1      1      0      0      b3
 *     1      1      0      1      b3
 *     1      1      1      0      b3
 *     1      1      1      1      b3
 */

/*
 * Pairs truth-table/literal
 */
typedef struct gmap_entry_s {
  uint32_t ttbl;
  literal_t lit;
} gmap_entry_t;

/*
 * Table element:
 * - key = array of 4 variables
 * - size and capacity
 * - data = array of pairs
 */
typedef struct gmap_elem_s {
  bvar_t var[4];        // key
  uint32_t size;        // size of the data array
  uint32_t nelems;      // number of elements in array data
  gmap_entry_t data[0]; // real size given by size.
} gmap_elem_t;


#define GMAP_ELEM_DEF_SIZE 2
#define GMAP_ELEM_MAX_SIZE ((uint32_t)((UINT32_MAX-sizeof(gmap_elem_t))/sizeof(gmap_entry_t)))

/*
 * Hash table
 */
typedef struct gmap_s {
  gmap_elem_t **data;
  uint32_t size;       // power of two
  uint32_t nelems;     // number of elements in the table
  uint32_t resize_threshold;
} gmap_t;


#define GMAP_DEF_SIZE 1024
#define GMAP_MAX_SIZE (UINT32_MAX/sizeof(gmap_elem_t *))
#define GMAP_RESIZE_RATIO 0.6
/*
 * Initialization:
 * - n: initial size. Must be 0 or a power of 2.
 * - if n is 0, the default is used.
 */
extern void init_gmap(gmap_t *gmap, uint32_t n);

/*
 * Delete: free memory
 */
extern void delete_gmap(gmap_t *gmap);

/*
 * Reset: empty the table
 */
extern void reset_gmap(gmap_t *gmap);

/*
 * Search for a gate g and return the literal mapped to g.
 * If g is not in the table, return null_literal.
 */
extern literal_t gmap_find(const gmap_t *gmap, const bgate_t *g);

/*
 * Search for a gate g and return the literal mapped to g.
 * If g is not in the table, add the gate and map it to l then return l.
 */
extern literal_t gmap_get(gmap_t *gmap, const bgate_t *g, literal_t l);

/*
 * Variants: use ttbl instead of a gate g
 * - ttbl must be normalized
 */
extern literal_t gmap_find_ttbl(const gmap_t *gmap, const ttbl_t *tt);
extern literal_t gmap_get_ttbl(gmap_t *gmap, const ttbl_t *tt, literal_t l);


/*
 * More variants: use a wide truth table
 * - w must be normalized and have no more than four variables.
 */
extern literal_t gmap_find_wide_ttbl(const gmap_t *gmap, const wide_ttbl_t *w);
extern literal_t gmap_get_wide_ttbl(gmap_t *gmap, const wide_ttbl_t *w, literal_t l);



#endif /* __NEG_GATE_HASH_MAP2_H */
