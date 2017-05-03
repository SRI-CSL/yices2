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
 * VECTORS TO STORE A MAP FROM 32BIT INDICES TO 8BIT VALUES
 */

#ifndef __MARK_VECTORS_H
#define __MARK_VECTORS_H

#include <stdint.h>
#include <assert.h>


/*
 * Vector:
 * - def = default value
 * - map = current map
 * - size = size of the map array
 * - end_map = largest index mapped in map + 1
 * The mark of an index i>=0 is
 * - map[i] if i < end_map
 * - def otherwise
 * - we always have end_map <= size
 */
typedef struct mark_vector_s {
  uint8_t *map;
  uint32_t end_map;
  uint32_t start_map;
  uint32_t size;
  uint8_t def;
} mark_vector_t;


/*
 * Initialization:
 * - d = default value
 * - n = initial size of the map array
 * (initial map: everything is mapped to d)
 */
extern void init_mark_vector(mark_vector_t *v, uint32_t n, uint8_t d);


/*
 * Reset to the initial map: everything mapped to v->def
 */
static inline void reset_mark_vector(mark_vector_t *v) {
  if (v->start_map < v->end_map) {
    v->end_map = v->start_map;
  } else {
    v->end_map = 0;
  }
}

/*
 * Delete: free memory
 */
extern void delete_mark_vector(mark_vector_t *v);


/*
 * Add map [i --> x] to v
 * - i must be non-negative
 * - overwrite the current value of i if any
 */
extern void mark_vector_add_mark(mark_vector_t *v, int32_t i, uint32_t x);


/*
 * Get the value mapped to i
 * - i must be non-negative
 */
static inline uint8_t mark_vector_get_mark(mark_vector_t *v, int32_t i) {
  assert(i >= 0);
  return (i < v->end_map) ? v->map[i] : v->def;
}


#endif /* __MARK_VECTORS_H */
