/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * Table to map integer keys to an array of integers (vector)
 */

#ifndef __VECTOR_HASH_MAP_H
#define __VECTOR_HASH_MAP_H

#include <stdint.h>

/*
 * Vector in the table are pairs <key, vector>
 * - the vector itself consists of a header: nelems + size
 *   followed by an array data of size elements.
 */
typedef struct vhmap_vector_s {
  int32_t key;
  uint32_t size;
  uint32_t nelems;
  int32_t data[0];  // real size = size
} vhmap_vector_t;


/*
 * Default and max sizes of a vector
 */
#define DEF_VHMAP_VECTOR_SIZE 10
#define MAX_VHMAP_VECTOR_SIZE ((uint32_t)((UINT32_MAX-sizeof(vhmap_vector_t))/sizeof(int32_t)))


/*
 * Hash table:
 * - only supports addition
 */
typedef struct vector_hmap_s {
  vhmap_vector_t **data;
  uint32_t size;   // power of 2
  uint32_t nelems; // number of vector stored
  uint32_t resize_threshold; // resize_ratio * size
} vector_hmap_t;


/*
 * Default and max sizes for the table
 */
#define DEF_VECTOR_HMAP_SIZE 32
#define MAX_VECTOR_HMAP_SIZE ((uint32_t)(UINT32_MAX/sizeof(vhmap_vector_t *)))

#define VECTOR_HMAP_RESIZE_RATIO 0.6


/*
 * Initialization:
 * - n = initial size. It must be a power of 2 or 0.
 * - if n = 0, the default size is used.
 */
extern void init_vector_hmap(vector_hmap_t *hmap, uint32_t n);

/*
 * Empty the table
 */
extern void reset_vector_hmap(vector_hmap_t *hmap);

/*
 * Delete: free memory
 */
extern void delete_vector_hmap(vector_hmap_t *hmap);

/*
 * Get the vector of key k
 * - return NULL if there's no vector of key k
 */
extern vhmap_vector_t *vector_hmap_find(const vector_hmap_t *hmap, int32_t k);

/*
 * Add element x to the vector of key k
 * - this creates a new vector if k is not already in the table.
 */
extern void vector_hmap_add(vector_hmap_t *hmap, int32_t k, int32_t x);


/*
 * Direct access to the entries. 
 *
 * This is intended for scanning the table:
 *
 *    n = vector_hmap_size(hmap);
 *    for (i=0; i<n; i++) {
 *      v = vector_hmap_entry(hmap, i);
 *      if (v != NULL) {
 *         ...
 *      }
 *   }
 *
 */
static inline uint32_t vector_hmap_size(vector_hmap_t *hmap) {
  return hmap->size;
}

static inline vhmap_vector_t *vector_hmap_entry(vector_hmap_t *hmap, uint32_t i) {
  assert(i < hmap->size);
  return hmap->data[i];
}


#endif /* __VECTOR_HASH_MAP_H */
