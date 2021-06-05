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
 * HASH CONSING FOR ARRAYS OF INTEGERS
 */

#ifndef __INT_ARRAY_HSETS_H
#define __INT_ARRAY_HSETS_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Array descriptor:
 * - hash = hash code
 * - nelems = number of elements
 * - data = array of elements
 */
typedef struct harray_s {
  uint32_t hash;
  uint32_t nelems;
  int32_t data[0]; // real size = nelems
} harray_t;

#define MAX_HARRAY_SIZE ((UINT32_MAX-sizeof(harray_t))/sizeof(int32_t))


/*
 * Table of arrays for hash consing
 */
typedef struct int_array_hset_s {
  harray_t **data;
  uint32_t size;
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} int_array_hset_t;


/*
 * Default and max size
 */
#define DEF_INT_ARRAY_HSET_SIZE 64
#define MAX_INT_ARRAY_HSET_SIZE (UINT32_MAX/sizeof(harray_t*))

/*
 * Ratios: resize_threshold = size * RESIZE_RATIO
 *         cleanup_threshold = size * CLEANUP_RATIO
 */
#define INT_ARRAY_HSET_RESIZE_RATIO 0.6
#define INT_ARRAY_HSET_CLEANUP_RATIO 0.2

/*
 * Marker for deleted sets
 */
#define DELETED_HARRAY ((harray_t *) 1)


/*
 * Initialize a set
 * - n = initial size: must be a power of 2
 * - if n = 0 the default size is used
 */
extern void init_int_array_hset(int_array_hset_t *set, uint32_t n);


/*
 * Delete
 */
extern void delete_int_array_hset(int_array_hset_t *set);


/*
 * Empty the set
 */
extern void reset_int_array_hset(int_array_hset_t *set);


/*
 * Find array a[0 .. n-1]
 * - a[0 ... n-1] must be an array of n elements
 * - return NULL if it's not in the set
 */
extern harray_t *int_array_hset_find(const int_array_hset_t *set, uint32_t n, const int32_t *a);


/*
 * Get descriptor for a[0 ... n-1]. Create it if it's not in set already.
 */
extern harray_t *int_array_hset_get(int_array_hset_t *set, uint32_t n, const int32_t *a);


/*
 * Remove set a[0...n-1] from the set
 * - no change if a is not present
 */
extern void int_array_hset_remove(int_array_hset_t *set, uint32_t n, const int32_t *a);


/*
 * Remove all arrays that satisfy f
 * - for every array a in the table, call f(aux, a)
 * - if that returns true, then a is deleted
 * - f must not have side effects
 */
typedef bool (*int_array_hset_filter_t)(void *aux, const harray_t *a);

extern void int_array_hset_remove_arrays(int_array_hset_t *set, void *aux, int_array_hset_filter_t f);



#endif /* __INT_ARRAY_HSETS_H */
