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
 * Hash table that maps non-negative integers to rationals.
 * This is used in the difference-logic profiler.
 *
 * This implementation supports only addition and query (not removal
 * of entries).
 */

#ifndef __INT_RATIONAL_HASH_MAPS_H
#define __INT_RATIONAL_HASH_MAPS_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/rationals.h"

/*
 * Records stored in the table = pairs integer, rational.
 * - if key is -1, the entry is empty (and the rational is 0)
 * - otherwise the key must be non-negative.
 */
typedef struct int_rat_hmap_rec_s {
  int32_t key;
  rational_t value;
} int_rat_hmap_rec_t;

/*
 * Hash table
 * - data = table proper
 * - size = its size (always a power of two)
 * - nelems = number of non-empty entries in the table
 * - resize_threshold = threshold to trigger resizing:
 *   when nelems >= resize_threshold, we double the
 *   table size.
 */
typedef struct int_rat_hmap_s {
  int_rat_hmap_rec_t *data;
  uint32_t size;
  uint32_t nelems;
  uint32_t resize_threshold;
} int_rat_hmap_t;


/*
 * Default initial size and maximal size
 */
#define INT_RAT_HMAP_DEF_SIZE 32
#define INT_RAT_HMAP_MAX_SIZE (UINT32_MAX/sizeof(int_rat_hmap_rec_t))

/*
 * Ratio: resize_threshold = size * RESIZE_RATIO
 */
#define INT_RAT_HMAP_RESIZE_RATIO 0.6

/*
 * Initialization:
 * - n = initial size, must be a power of 2
 * - if n = 0, the default size is used
 */
extern void init_int_rat_hmap(int_rat_hmap_t *hmap, uint32_t n);

/*
 * Delete: free memory
 */
extern void delete_int_rat_hmap(int_rat_hmap_t *hmap);

/*
 * Find record with key k. Return NULL if there's none.
 * - k must be non-negative.
 *
 * Important: the returned pointer may become invalid if more
 * elements are added to the table.
 */
extern int_rat_hmap_rec_t *int_rat_hmap_find(int_rat_hmap_t *hmap, int32_t k);

/*
 * Get record with key k
 * - if one is in the table return it and set *new to false.
 * - otherwise, create a fresh record with key k, value 0, 
 *   and  set *new to true.
 * - k must be non-negative.
 *
 * Important: the returned pointer may become invalid if more
 * elements are added to the table.
 */
extern int_rat_hmap_rec_t *int_rat_hmap_get(int_rat_hmap_t *hmap, int32_t k, bool *new);

/*
 * Remove all records
 */
extern void reset_int_rat_hmap(int_rat_hmap_t *hmap);

/*
 * Compute the sum of all values
 */
extern void int_rat_hmap_sum(int_rat_hmap_t *hmap, rational_t *sum);


#endif /* __INT_RATIONAL_HASH_MAPS_H */
