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
 * - map pairs of 32bit integers to non-null pointers
 */

#ifndef __PAIR_HASH_MAP_H
#define __PAIR_HASH_MAP_H

#include <stdint.h>

/*
 * Records stored in the hash table include
 * - key = pair k0, k1
 * - value = pointer
 * Empty records are marked by setting val == NULL
 * Deleted records are marked by setting val == DELETED_PTR
 */
typedef struct pmap_rec_s {
  int32_t k0;
  int32_t k1;
  void *val;
} pmap_rec_t;

/*
 * Marker for deleted records
 */
#define DELETED_PTR ((void *) 1)

/*
 * Default pointer value for records created by pair_hmap_get
 */
#define DEFAULT_PTR ((void *) 3)


/*
 * Usual hash-map components:
 * - data = hash table proper
 * - size = size of the array data
 * - nelems = number of records present
 * - ndeleted = number of deleted records
 */
typedef struct pmap_s {
  pmap_rec_t *data;
  uint32_t size; // must be a power of 2
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} pmap_t;


/*
 * Default initial size
 */
#define PMAP_DEFAULT_SIZE 32
#define PMAP_MAX_SIZE (UINT32_MAX/16)

/*
 * Ratios: resize_threshold = size * RESIZE_RATIO
 *         cleanup_threshold = size * CLEANUP_RATIO
 */
#define PMAP_RESIZE_RATIO 0.6
#define PMAP_CLEANUP_RATIO 0.2

/*
 * Initialization:
 * - n = initial size, must be a power of 2
 * - if n = 0, the default size is used
 */
extern void init_pmap(pmap_t *hmap, uint32_t n);

/*
 * Delete: free memory
 */
extern void delete_pmap(pmap_t *hmap);

/*
 * Find record with key (k0, k1). Return NULL if there's none
 */
extern pmap_rec_t *pmap_find(const pmap_t *hmap, int32_t k0, int32_t k1);

/*
 * Get record with key (k0, k1). If one is in the table return it.
 * Otherwise, add a fresh record with key k0, k1 and value DEFAULT_PTR
 * and return it.
 */
extern pmap_rec_t *pmap_get(pmap_t *hmap, int32_t k0, int32_t k1);

/*
 * Erase record r
 */
extern void pmap_erase(pmap_t *hmap, pmap_rec_t *r);

/*
 * Remove all records
 */
extern void pmap_reset(pmap_t *hmap);

/*
 * Support for scanning all records:
 * - first gives the first valid record (value field is not NULL nor DELETED_PTR) or NULL
 * - next(p) gives the next record after p or NULL
 * IMPORTANT: The hmap must not be modified between calls to next
 */
extern pmap_rec_t *pmap_first_record(pmap_t *hmap);
extern pmap_rec_t *pmap_next_record(pmap_t *hmap, pmap_rec_t *p);

#endif /* __PAIR_HASH_MAP_H */
