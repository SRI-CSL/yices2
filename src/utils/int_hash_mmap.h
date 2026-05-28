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
* HASH MAPS with multi key support
*
* keys and values are signed 32bit integers that must be non-negative.
*/

#ifndef __INT_HASH_MMAP_H
#define __INT_HASH_MMAP_H

#include <stdint.h>
#include <stdbool.h>

#include "utils/int_vectors.h"


/*
* Records stored in the hash table are pairs of integers
* - key is >= 0
*/
typedef struct int_hmmap_pair_s {
  int32_t key;
  int32_t val;
} int_hmmap_pair_t;

typedef struct int_hmmap_s {
  int_hmmap_pair_t *data;
  uint32_t size; // must be a power of 2
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} int_hmmap_t;


/*
* Default initial size
*/
#define INT_HMMAP_DEFAULT_SIZE 32
#define INT_HMMAP_MAX_SIZE (UINT32_MAX/8)

/*
* Ratios: resize_threshold = size * RESIZE_RATIO
*         cleanup_threshold = size * CLEANUP_RATIO
*/
#define INT_HMMAP_RESIZE_RATIO 0.6
#define INT_HMMAP_CLEANUP_RATIO 0.2


/*
* Initialization:
* - n = initial size, must be 0 or a power of 2
* - if n = 0, the default size is used
*/
extern void init_int_hmmap(int_hmmap_t *hmmap, uint32_t n);


/*
* Delete: free memory
*/
extern void delete_int_hmmap(int_hmmap_t *hmmap);


/*
 * Find the n-th record with key k
 * - return NULL if not found
 */
extern int_hmmap_pair_t *int_hmmap_find(const int_hmmap_t *hmmap, int32_t k, uint32_t n);


/*
 * Add record [k -> v]
 */
extern void int_hmmap_add(int_hmmap_t *hmmap, int32_t k, int32_t v);

/*
 * Add record [k -> v] if it is not found
 */
bool int_hmmap_insert(int_hmmap_t *hmmap, int32_t k, int32_t v);

/*
 * Checks if map contains k -> v
 */
extern bool int_hmmap_contains(const int_hmmap_t *hmmap, int32_t k, int32_t v);


/*
* Erase record r
*/
extern void int_hmmap_erase(int_hmmap_t *hmmap, int_hmmap_pair_t *r);


/*
* Remove all records
*/
extern void int_hmmap_reset(int_hmmap_t *hmmap);


/*
 * Finds all values of k and adds them to v.
 * Returns the number of found elements.
 */
extern uint32_t int_hmmap_find_all(int_hmmap_t *hmmap, int32_t k, ivector_t *v);


/*
 * Inserts all elements of v with key k.
 */
extern void int_hmmap_add_all(int_hmmap_t * hmmap, int32_t k, const ivector_t *v);


bool int_hmmap_contains_key(const int_hmmap_t *hmmap, int32_t k);



#endif /* __INT_HASH_MMAP_H */
