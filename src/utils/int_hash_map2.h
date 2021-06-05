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
 * Maps pairs of 32bit integers to 32bit integers.
 * The keys must be non-negative.
 *
 * Supported operations: addition/query/garbage collection.
 * Removal of individual records is not supported.
 */

#ifndef __INT_HASH_MAP2_H
#define __INT_HASH_MAP2_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Records stored in the hash table are triples of integers
 * - key pair: k0, k1 (both are non-negative)
 * - value = signed integer
 */
typedef struct int_hmap2_rec_s {
  int32_t k0;
  int32_t k1;
  int32_t val;
} int_hmap2_rec_t;

/*
 * Markers for empty records (stored in k0)
 */
enum {
  INT_HMAP2_EMPTY = -1,
};


/*
 * Hash-table components:
 * - data = table proper
 * - size = its size
 * - nelems = number of elements stored
 *   (i.e., elements of the data array whose k0 field is >= 0).
 * - resize_threshold = threshold to trigger resizing
 *   when nelems >= resize_threshold, the table's size is
 *   doubled.
 */
typedef struct int_hmap2_s {
  int_hmap2_rec_t *data;
  uint32_t size;    // must be a power of 2
  uint32_t nelems;
  uint32_t resize_threshold;
} int_hmap2_t;


/*
 * Default initial size and maximal size
 */
#define INT_HMAP2_DEF_SIZE 32
#define INT_HMAP2_MAX_SIZE (UINT32_MAX/sizeof(int_hmap2_rec_t))

/*
 * Ratio: resize_threshold = size * RESIZE_RATIO
 */
#define INT_HMAP2_RESIZE_RATIO 0.6


/*
 * Initialization:
 * - n = initial size, must be a power of 2
 * - if n = 0, the default size is used
 */
extern void init_int_hmap2(int_hmap2_t *hmap, uint32_t n);

/*
 * Delete: free memory
 */
extern void delete_int_hmap2(int_hmap2_t *hmap);

/*
 * Find record with key (k0, k1). Return NULL if there's none.
 * - k0 and k1 must be non-negative.
 */
extern int_hmap2_rec_t *int_hmap2_find(const int_hmap2_t *hmap, int32_t k0, int32_t k1);

/*
 * Get record with key (k0, k1).
 * - if one is in the table return it and set *new to false.
 * - otherwise, create a fresh record with key (k0, k1), and
 *   set *new to true.
 * If a new record is created, val is not initialized.
 * - k0 and k1 must be non-negative.
 */
extern int_hmap2_rec_t *int_hmap2_get(int_hmap2_t *hmap, int32_t k0, int32_t k1, bool *new);


/*
 * Add record (k0, k1 :-> val)
 * - there must not be a record with the same key pair
 */
extern void int_hmap2_add(int_hmap2_t *hmap, int32_t k0, int32_t k1, int32_t val);



/*
 * Remove all records
 */
extern void reset_int_hmap2(int_hmap2_t *hmap);


/*
 * Support for garbage collection:
 * - keep_alive is a function that indicates whether a
 *   record should be kept or not.
 * - aux is an auxiliary pointer passed as argument to keep_alive
 * The garbage collection function scans all records in the table,
 * calls keep_alive(aux, r) on every record r, and removes r if
 * keep_alive returns false.
 */
typedef bool (*keep_alive_fun_t)(void *aux, int_hmap2_rec_t *r);

extern void int_hmap2_gc(int_hmap2_t *hmap, void *aux, keep_alive_fun_t f);


#endif /* __INT_HASH_MAP2_H */
