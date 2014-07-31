/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
extern pmap_rec_t *pmap_find(pmap_t *hmap, int32_t k0, int32_t k1);

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


#endif /* __PAIR_HASH_MAP_H */
