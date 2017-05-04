/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
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
 * Vector that stores a map from 32bit indices to 8bit values
 * - this is a variant of mark_vectors.h intended to be more
 *   efficient (to be used by the sat solver)
 * - the default value is map[x] = 0 for all x
 * - the implementation assumes that map is sparse:
 *     map[x] is 0 for most x
 *     map[x] /= 0 for a small number of indices x
 * - for fast reset, we keep track of all x's such that
 *   map[x] /= 0 in an internal vector.
 */

#ifndef __TAG_MAP_H
#define __TAG_MAP_H

#include <stdint.h>
#include <assert.h>

#include "utils/int_vectors.h"

/*
 * Data structure:
 * - map[x] = value for x
 * - marked = vector of all x's such that map[x] != 0
 * - size = size of the map array
 */
typedef struct tag_map_s {
  uint8_t *map;
  ivector_t marked;
  uint32_t size;
} tag_map_t;

// MAX SIZE is UINT32_MAX
#define DEF_TAG_MAP_SIZE 100


/*
 * Initialize a map of size n
 * - if n=0, the default size is used
 */
extern void init_tag_map(tag_map_t *map, uint32_t n);

/*
 * Free all memory used
 */
extern void delete_tag_map(tag_map_t *map);

/*
 * Set map[x] := v
 * - v must be positive
 * - resize the map if necessary to store map[x]
 */
extern void tag_map_write(tag_map_t *map, uint32_t x, uint8_t v);

/*
 * Clear: reset map[x] to zero for all x
 */
extern void clear_tag_map(tag_map_t *map);


/*
 * Get the value mapped to x
 */
static inline uint8_t tag_map_read(const tag_map_t *map, uint32_t x) {
  return (x < map->size) ? map->map[x] : 0;
}


/*
 * Cardinality: number of x whose value is non-zero
 */
static inline uint32_t tag_map_size(const tag_map_t *map) {
  return map->marked.size;
}


/*
 * Direct access if x is known to be between 0 and map->size
 */
static inline uint8_t tag_map_get(const tag_map_t *map, uint32_t x) {
  assert(x < map->size);
  return map->map[x];
}


/*
 * Overwrite: assumes that x is already in the map->marked vector
 */
static inline void tag_map_set(tag_map_t *map, uint32_t x, uint8_t v) {
  assert(x < map->size && map->map[x] > 0 && v > 0);
  map->map[x] = v;
}


#endif /* __TAG_MAP_H */
