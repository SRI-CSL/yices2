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
 * ARRAYS OF INTEGERS WITH REFERENCE COUNTERS
 */

#ifndef __REFCOUNT_INT_ARRAYS_H
#define __REFCOUNT_INT_ARRAYS_H

#include <stdint.h>
#include <stddef.h>


/*
 * Array header
 */
typedef struct {
  uint32_t ref;     // no check for overflow is implemented
  int32_t  data[0]; // real size is determined at allocation time
} int_array_t;


#define MAX_REFCOUNT_INT_ARRAY_SIZE ((UINT32_MAX-sizeof(int_array_t))/sizeof(int32_t))


/*
 * Allocate a fresh array of n elements
 * - initialize the reference counter to 0
 */
extern int32_t *alloc_int_array(uint32_t n);


/*
 * Get the header of a
 */
static inline int_array_t *int_array_header(int32_t *a) {
  return (int_array_t *) (((char *) a) - offsetof(int_array_t, data));
}

/*
 * Increment the reference counter
 */
static inline void int_array_incref(int32_t *a) {
  int_array_header(a)->ref ++;
}


/*
 * If a is NULL, do nothing. Otherwise, decrement a's reference counter
 * and free the array if the counter becomes zero.
 */
extern void int_array_decref(int32_t *a);


#endif /* __REFCOUNT_INT_ARRAYS_H */
