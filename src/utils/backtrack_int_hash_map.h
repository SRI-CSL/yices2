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
 * HASH MAPS WITH SUPPORT FOR PUSH/POP
 *
 * keys and values are signed 32bit integers that must be non-negative.
 */

#ifndef __BACKTRACK_INT_HASH_MAP_H
#define __BACKTRACK_INT_HASH_MAP_H

#include <stdint.h>


/*
 * Records stored in the table
 */
typedef struct back_hmap_elem_s {
  int32_t key;
  int32_t val;
} back_hmap_elem_t;


/*
 * Markers for empty and deleted pairs
 */
enum {
  BACK_HMAP_EMPTY_KEY = -1,
  BACK_HMAP_DELETED_KEY = -2,
};


/*
 * map = two arrays of the same size
 * - pair = array of pairs (key, value)
 * - level = array of unsigned integer
 * - if pair[i] contains a pair (k, v) with k>=0
 *   then level[i] is the base_level at which the pair was added to the table.
 * - when we backtrack from a level b, we delete pair[i] if level[i] == b.
 */
typedef struct back_hmap_data_s {
  back_hmap_elem_t *pair;
  uint32_t *level;
} back_hmap_data_t;


/*
 * Full table: size is a power of 2
 * - nelems = number of elements stored in the table (i.e., data.pair[i].key >= 0)
 * - ndeleted = number of deleted elements (i.e., data.pair[i].key == -2).
 */
typedef struct back_hmap_s {
  back_hmap_data_t data;
  uint32_t size;
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
  uint32_t level;
} back_hmap_t;


#define BACK_HMAP_DEF_SIZE 32
#define BACK_HMAP_MAX_SIZE (UINT32_MAX/sizeof(back_hmap_elem_t))

#define BACK_HMAP_RESIZE_RATIO 0.6
#define BACK_HMAP_CLEANUP_RATIO 0.2


/*
 * Initialization
 * - n = initialize size. It must be 0 or a power of 2.
 * - if n is zero, the default is used.
 * - base_level is set to 0.
 */
extern void init_back_hmap(back_hmap_t *hmap, uint32_t n);


/*
 * Delete: free memory
 */
extern void delete_back_hmap(back_hmap_t *hmap);


/*
 * Reset: empty the table and reset level to 0
 */
extern void reset_back_hmap(back_hmap_t *hmap);


/*
 * Increase level
 */
static inline void back_hmap_push(back_hmap_t *hmap) {
  hmap->level ++;
}


/*
 * Set the level to n
 * - this can be use to set the initial level to something other than 0.
 */
static inline void back_hmap_set_level(back_hmap_t *hmap, uint32_t n) {
  hmap->level = n;
}


/*
 * Backtrack to the previous level: remove all elements
 * added at the current level.
 * - hmap->level must be positive
 */
extern void back_hmap_pop(back_hmap_t *hmap);


/*
 * Find record with key k. Return NULL if this key is not in the map.
 */
extern back_hmap_elem_t *back_hmap_find(const back_hmap_t *hmap, int32_t k);


/*
 * Get record with key k. If there's no such record, create a new one
 * with key = k, val = -1, and level = current hmap level.
 */
extern back_hmap_elem_t *back_hmap_get(back_hmap_t *hmap, int32_t k);


#endif /* __BACKTRACK_INT_HASH_MAP_H */
