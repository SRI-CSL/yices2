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
 * Sets of unsigned 32-bit numbers
 * - only supports addition of elements
 */

#ifndef __INT_HASH_SET_H
#define __INT_HASH_SET_H

#include <stdint.h>
#include <stdbool.h>


/*
 * - data: array of 2^n elements (hash table)
 * - z_flag: boolean flag, true if 0 has been
 *   added to the set (0 is used as a marker
 *   so it cannot be stored in data).
 * - nelems: number of elements in array data
 *   = number of non-zero elements in the set
 * - size = 2^n = size of array data
 *
 * - resize threshold: the table is extended
 *   when nelems > resize_threshold
 */
typedef struct int_hset_s {
  uint32_t *data;
  uint32_t size;
  uint32_t nelems;
  bool z_flag;
  uint32_t resize_threshold;
} int_hset_t;


/*
 * Default initial size (must be a power of 2)
 */
#define INT_HSET_DEFAULT_SIZE 64

/*
 * Maximal size
 */
#define MAX_HSET_SIZE (UINT32_MAX/sizeof(uint32_t))


/*
 * Resize threshold: the size is doubled
 * when nelems >= size * RESIZE_RATIO
 */
#define INT_HSET_RESIZE_RATIO 0.7


/*
 * Shrink size: when reset is called, the array is
 * resized to the default size
 */
#define INT_HSET_SHRINK_SIZE 2048


/*
 * Initialize the set with n = initial size
 * n must be a power of 2
 * - if n=0, the default size is used.
 */
extern void init_int_hset(int_hset_t *set, uint32_t n);


/*
 * Free memory
 */
extern void delete_int_hset(int_hset_t *set);


/*
 * Check whether s is empty
 */
static inline bool int_hset_is_nonempty(int_hset_t *set) {
  return (set->z_flag || set->nelems > 0);
}

static inline bool int_hset_is_empty(int_hset_t *set) {
  return !int_hset_is_nonempty(set);
}


/*
 * Check whether x is in set s
 */
extern bool int_hset_member(int_hset_t *set, uint32_t x);


/*
 * Add element x to set
 * - return true if x is not already in s
 * - return false if x is already in s
 */
extern bool int_hset_add(int_hset_t *set, uint32_t x);


/*
 * Close the set: compact the data
 * - all elements get stored in data[0 ... nelems]
 *   (including zero if it's present)
 * - no addition is supported after compaction
 * - calls to int_hset_member will also fail
 */
extern void int_hset_close(int_hset_t *set);


/*
 * Close the set and sort it
 * 1) move all non-zero elements in data[0 ... nelems-1]
 * 2) sort data[0 ... nelems-1]
 * 3) if z_flag is set, copy 0 into data[nelems], then increment nelems
 */
extern void int_hset_close_and_sort(int_hset_t *set);

/*
 * Empty the set
 */
extern void int_hset_reset(int_hset_t *set);


#endif /* __INT_HASH_SET_H */
