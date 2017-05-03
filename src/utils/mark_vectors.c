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

#include <string.h>

#include "utils/mark_vectors.h"
#include "utils/memalloc.h"


/*
 * Initialization:
 * - d = default value
 * - n = initial size of the data array
 * (initial map: everything is mapped to d)
 */
void init_mark_vector(mark_vector_t *v, uint32_t n, uint8_t d) {
  uint8_t *tmp;

  tmp = NULL;
  if (n > 0) {
    tmp = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  }
  v->map = tmp;
  v->end_map = 0;
  v->start_map = UINT32_MAX;
  v->size = n;
  v->def = d;
}


/*
 * Free memory
 */
void delete_mark_vector(mark_vector_t *v) {
  safe_free(v->map);
  v->map = NULL;
}



/*
 * Make map large enough to store map[i]
 */
static void extend_mark_vector(mark_vector_t *v, int32_t i) {
  uint32_t n;

  assert(0 <= i);

  // try to grow map by 50%.
  // if that's not enough use i+1 as the new size
  n = v->size + 1;
  n += (n >> 1);
  if (n <= i) {
    n = i+1;
  }

  assert(i < n);
  v->map = (uint8_t *) safe_realloc(v->map, n * sizeof(uint8_t));
  v->size = n;
}


/*
 * Add map [i --> x] to v
 * - i must be non-negative
 * - overwrite the current value of i if any
 */
void mark_vector_add_mark(mark_vector_t *v, int32_t i, uint32_t x) {
  uint32_t n;

  assert(i >= 0);

  n = v->end_map;
  if (i >= n) {
    if (i >= v->size) {
      extend_mark_vector(v, i);
    }
    memset(v->map + v->end_map, v->def, i - n);
    v->end_map = ((uint32_t) i) + 1;
  }
  if (i < v->start_map) {
    v->start_map = i;
  }
  v->map[i] = x;
}

