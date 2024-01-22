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
 * keys are MCSAT values and values are signed 32bit integers that must
 * be non-negative.
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

#include "mcsat/value.h"

/*
 * Records stored in the hash table are pairs of integers
 * - key is >= 0
 */
typedef struct value_hmap_pair_s {
  mcsat_value_t* key;
  int32_t val;
} value_hmap_pair_t;

typedef struct value_hmap_s {
  value_hmap_pair_t *data;
  uint32_t size; // must be a power of 2
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} value_hmap_t;


/*
 * Default initial size
 */
#define VALUE_HMAP_DEFAULT_SIZE 32
#define VALUE_HMAP_MAX_SIZE (UINT32_MAX/8)

/*
 * Ratios: resize_threshold = size * RESIZE_RATIO
 *         cleanup_threshold = size * CLEANUP_RATIO
 */
#define VALUE_HMAP_RESIZE_RATIO 0.6
#define VALUE_HMAP_CLEANUP_RATIO 0.2


/*
 * Initialization:
 * - n = initial size, must be 0 or a power of 2
 * - if n = 0, the default size is used
 */
void init_value_hmap(value_hmap_t *hmap, uint32_t n);


/*
 * Delete: free memory
 */
void delete_value_hmap(value_hmap_t *hmap);


/*
 * Find record with key k. Return NULL if there's none
 */
value_hmap_pair_t *value_hmap_find(const value_hmap_t *hmap, const mcsat_value_t* k);


/*
 * Get record with key k. If one is in the table return it.
 * Otherwise, add a fresh record with key k and value -1 and return it.
 */
value_hmap_pair_t *value_hmap_get(value_hmap_t *hmap, const mcsat_value_t* k);


/*
 * Add record [k -> v]
 * - there must not be a record with the same key
 */
void value_hmap_add(value_hmap_t *hmap, const mcsat_value_t* k, int32_t v);


/*
 * Erase record r
 */
void value_hmap_erase(value_hmap_t *hmap, value_hmap_pair_t *r);


/*
 * Remove all records
 */
void value_hmap_reset(value_hmap_t *hmap);


/*
 * Remove all records that satisfy f
 * - calls f(aux, p) on every record p stored in hmap
 * - if f(aux, p) returns true then record p is removed
 */
typedef bool (*value_hmap_filter_t)(void *aux, const value_hmap_pair_t *p);

void value_hmap_remove_records(value_hmap_t *hmap, void *aux, value_hmap_filter_t f);


/*
 * Updates the value of the records
 * - calls f(aux, p) on every record p stored in hmap
 * - p->val is set according to the return value of f(aux, p)
 */
typedef uint32_t (*value_hmap_map_t)(void *aux, const value_hmap_pair_t *p);

void value_hmap_update_records(value_hmap_t *hmap, void *aux, value_hmap_map_t f);


/*
 * Iterator: call f(aux, p) on every record p stored in hmap
 * - f must not have any side effect on the hmap
 */
typedef void (*value_hmap_iterator_t)(void *aux, const value_hmap_pair_t *p);

void value_hmap_iterate(value_hmap_t *hmap, void *aux, value_hmap_iterator_t f);


/*
 * Support for scanning all records:
 * - first gives the first non-null record in the table or NULL
 * - next(p) gives the next record after p or NULL
 * IMPORTANT: The hmap keys must not be modified between calls to next
 */
value_hmap_pair_t *value_hmap_first_record(value_hmap_t *hmap);
value_hmap_pair_t *value_hmap_next_record(value_hmap_t *hmap, value_hmap_pair_t *p);
