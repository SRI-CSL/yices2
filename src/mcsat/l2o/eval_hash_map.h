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
 * HASH MAPS
 *
 * keys are signed 32bit integers that must be non-negative; values are double
 * 
 * Adapted from int_hash_map
 */


#ifndef __EVAL_HASH_MAP_H
#define __EVAL_HASH_MAP_H

#include <stdint.h>
#include <stdbool.h>

/*
 * Records stored in the hash table are pairs of integers
 * - key is >= 0
 */
typedef struct eval_hmap_pair_s {
  int32_t key;
  double val;
} eval_hmap_pair_t;


typedef struct eval_hmap_s {
  eval_hmap_pair_t *data;
  uint32_t size; // must be a power of 2
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} eval_hmap_t;


/*
 * Default initial size
 */
#define EVAL_HMAP_DEFAULT_SIZE 32
#define EVAL_HMAP_MAX_SIZE (UINT32_MAX/8)

/*
 * Ratios: resize_threshold = size * RESIZE_RATIO
 *         cleanup_threshold = size * CLEANUP_RATIO
 */
#define EVAL_HMAP_RESIZE_RATIO 0.6
#define EVAL_HMAP_CLEANUP_RATIO 0.2


/*
 * Initialization:
 * - n = initial size, must be 0 or a power of 2
 * - if n = 0, the default size is used
 */
extern void init_eval_hmap(eval_hmap_t *hmap, uint32_t n);


/*
 * Delete: free memory
 */
extern void delete_eval_hmap(eval_hmap_t *hmap);


/*
 * Find record with key k. Return NULL if there's none
 */
extern eval_hmap_pair_t *eval_hmap_find(const eval_hmap_t *hmap, int32_t k);


/*
 * Get record with key k. If one is in the table return it.
 * Otherwise, add a fresh record with key k and value -1 and return it.
 */
extern eval_hmap_pair_t *eval_hmap_get(eval_hmap_t *hmap, int32_t k);


/*
 * Add record [k -> v]
 * - there must not be a record with the same key
 */
extern void eval_hmap_add(eval_hmap_t *hmap, int32_t k, double v);

/*
 * Add record [k -> v ] to hmap
 * - if there is a record with the same key, it is replaced by the new record
 */
void eval_hmap_add_replace(eval_hmap_t *hmap, int32_t k, double v);

/*
 * Add record [k -> v ] to hmap
 * - if there is a record with the same key, it does not replace it (but does not throw an error)
 */
void eval_hmap_add_not_replace(eval_hmap_t *hmap, int32_t k, double v);

/*
 * Erase record r
 */
extern void eval_hmap_erase(eval_hmap_t *hmap, eval_hmap_pair_t *r);


/*
 * Deep copy one map to another
 */
extern void eval_hmap_copy(eval_hmap_t *hmap_from, eval_hmap_t *hmap_to);


/*
 * Merge one map to another (do not overwrite duplicates)
 */
extern void eval_hmap_merge(eval_hmap_t *hmap_from, eval_hmap_t *hmap_to);

/*
 * Remove all records
 */
extern void eval_hmap_reset(eval_hmap_t *hmap);

#endif /* __EVAL_HASH_MAP_H */
