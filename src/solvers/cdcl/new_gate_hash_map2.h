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

/*
 * Keys are arrays of at most three Boolean variables var[0 .. 2].
 * Each key is mapped to a vector of pairs <truth-table, literal>
 * We use the same conventions as in truth_tables.h and new_gates.h.
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
 * - key
 * - size and capacity
 * - data = array of pairs
 */
typedef struct gmap_elem_s {
  bvar_t var[3];        // key
  uint32_t size;        // size of the data array
  uint32_t nelems;      // number of elements in array data
  gmap_entry_t data[0]; // real size givene by size.
} gmap_elem_t;


#define GMAP_ELEM_DEF_SIZE 2
#define GMAP_ELEM_MAX_SIZE ((uint32_t)((UINT32_MAX-sizeof(gmap_elem_t))/sizeof(gmap_entry_t)))

/*
 * Hash table
 */
typedef struct gmap_s {
  gmap_elem_t **data;
  uint32_t size;       // power of two
  uint32_t nelems;     // number of elements in tbe table
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


#endif /* __NEG_GATE_HASH_MAP2_H */
