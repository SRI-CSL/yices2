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
 * HASH TABLE FOR BOOLEAN GATES
 */

#ifndef __NEW_GATE_HASH_MAP_H
#define __NEW_GATE_HASH_MAP_H

#include <stdint.h>

#include "solvers/cdcl/new_gates.h"

/*
 * The keys are gate descriptors: represented by
 * - ttbl = 8 bit truth table
 * - var[3] = array of three boolean variables.
 * We store a map from keys to literals
 *
 * We use two arrays of size 2^n
 * - if key[i] is used then value[i] is the corresponding literal
 */
typedef struct gate_hmap_s {
  bgate_t *key;
  literal_t *value;
  uint32_t size;    // power of 2
  uint32_t nelems;  // number of entries in the table
  uint32_t resize_threshold;
} gate_hmap_t;


#define GATE_HMAP_DEF_SIZE 1024
#define GATE_HMAP_MAX_SIZE (UINT32_MAX/sizeof(bgate_t))
#define GATE_HMAP_RESIZE_RATIO 0.6

/*
 * Initialization:
 * - n: initial size. Must be 0 or a power of 2.
 * - if n is 0, the default is used.
 */
extern void init_gate_hmap(gate_hmap_t *hmap, uint32_t n);

/*
 * Delete: free memory
 */
extern void delete_gate_hmap(gate_hmap_t *hmap);

/*
 * Reset: empty the table
 */
extern void reset_gate_hmap(gate_hmap_t *hmap);

/*
 * Search for a gate g and return the literal mapped to g.
 * If g is not in the table, return null_literal.
 */
extern literal_t gate_hmap_find(const gate_hmap_t *hmap, const bgate_t *g);

/*
 * Add an entry to the map: the key is g, the value is l.
 * The key g must not be present in hmap.
 */
extern void gate_hmap_add(gate_hmap_t *hmap, const bgate_t *g, literal_t l);

/*
 * Variants: use ttbl instead of a gate g
 */
extern literal_t gate_hmap_find_ttbl(const gate_hmap_t *hmap, const ttbl_t *tt);
extern void gate_hmap_add_ttbl(gate_hmap_t *hmap, const ttbl_t *tt, literal_t l);


/*
 * Support for iterating through the table:
 * - first_gate returns a pointer to the first gate in hmap and return the corresponding literal in *lit
 * - next_gate returns a pointer to the gate that follows *g and return the corresponding literal in *lit
 * Both return NULL when  there's no more gate in the table
 */
extern bgate_t *gate_hmap_first_gate(const gate_hmap_t *hmap, literal_t *lit);
extern bgate_t *gate_hmap_next_gate(const gate_hmap_t *hamp, const bgate_t *g, literal_t *lit);


#endif /* __NEW_GATE_HASH_MAP_H */
