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
 * INTEGER ARRAYS WITH REFERENCE COUNTERS
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/refcount_int_arrays.h"


/*
 * Allocate an array of n elements
 * - set ref counter to zero
 */
int32_t *alloc_int_array(uint32_t n) {
  int_array_t *tmp;

  if (n > MAX_REFCOUNT_INT_ARRAY_SIZE) {
    out_of_memory();
  }

  tmp = (int_array_t *) safe_malloc(sizeof(int_array_t) + n * sizeof(int32_t));
  tmp->ref = 0;
  return tmp->data;
}


/*
 * Decrement the reference counter for a
 * - if the counter reaches zero, delete a
 */
void int_array_decref(int32_t *a) {
  int_array_t *h;

  if (a != NULL) {
    h = int_array_header(a);
    assert(h->ref > 0);
    h->ref --;
    if (h->ref == 0) free(h);
  }
}
