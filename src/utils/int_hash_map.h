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
 * keys and values are signed 32bit integers that must be non-negative.
 */

#ifndef __INT_HASH_MAP_H
#define __INT_HASH_MAP_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Records stored in the hash table are pairs of integers
 * - key is >= 0
 */
typedef struct int_hmap_pair_s {
  int32_t key;
  int32_t val;
} int_hmap_pair_t;

/*
 * Markers for empty/deleted pairs
 */
enum {
  DELETED_KEY = -2,
  EMPTY_KEY = -1,
};

typedef struct int_hmap_s {
  int_hmap_pair_t *data;
  uint32_t size; // must be a power of 2
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} int_hmap_t;


/*
 * Default initial size
 */
#define INT_HMAP_DEFAULT_SIZE 32
#define INT_HMAP_MAX_SIZE (UINT32_MAX/8)

/*
 * Ratios: resize_threshold = size * RESIZE_RATIO
 *         cleanup_threshold = size * CLEANUP_RATIO
 */
#define INT_HMAP_RESIZE_RATIO 0.6
#define INT_HMAP_CLEANUP_RATIO 0.2


/*
 * Initialization:
 * - n = initial size, must be 0 or a power of 2
 * - if n = 0, the default size is used
 */
extern void init_int_hmap(int_hmap_t *hmap, uint32_t n);


/*
 * Delete: free memory
 */
extern void delete_int_hmap(int_hmap_t *hmap);


/*
 * Find record with key k. Return NULL if there's none
 */
extern int_hmap_pair_t *int_hmap_find(const int_hmap_t *hmap, int32_t k);


/*
 * Get record with key k. If one is in the table return it.
 * Otherwise, add a fresh record with key k and value -1 and return it.
 */
extern int_hmap_pair_t *int_hmap_get(int_hmap_t *hmap, int32_t k);


/*
 * Add record [k -> v]
 * - there must not be a record with the same key
 */
extern void int_hmap_add(int_hmap_t *hmap, int32_t k, int32_t v);


/*
 * Erase record r
 */
extern void int_hmap_erase(int_hmap_t *hmap, int_hmap_pair_t *r);


/*
 * Remove all records
 */
extern void int_hmap_reset(int_hmap_t *hmap);



/*
 * Remove all records that satisfy f
 * - calls f(aux, p) on every record p stored in hmap
 * - if f(aux, p) returns true then record p is removed
 */
typedef bool (*int_hmap_filter_t)(void *aux, const int_hmap_pair_t *p);

extern void int_hmap_remove_records(int_hmap_t *hmap, void *aux, int_hmap_filter_t f);


/*
 * Iterator: call f(aux, p) on every record p stored in hmap
 * - f must not have any side effect on the hmap
 */
typedef void (*int_hmap_iterator_t)(void *aux, const int_hmap_pair_t *p);

extern void int_hmap_iterate(int_hmap_t *hmap, void *aux, int_hmap_iterator_t f);




/*
 * Support for scanning all records:
 * - first gives the first non-null record in the table or NULL
 * - next(p) gives the next record after p or NULL
 * IMPORTANT: The hmap must not be modified between calls to next
 */
extern int_hmap_pair_t *int_hmap_first_record(const int_hmap_t *hmap);
extern int_hmap_pair_t *int_hmap_next_record(const int_hmap_t *hmap, const int_hmap_pair_t *p);


#endif /* __INT_HASH_MAP_H */
