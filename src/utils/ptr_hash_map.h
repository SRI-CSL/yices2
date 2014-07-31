/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * MAPS 32BIT SIGNED INTEGERS TO POINTERS
 * keys are non-negative
 */

#ifndef __PTR_HASH_MAP_H
#define __PTR_HASH_MAP_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Records stored in the hash table are pairs key, val
 * - key is >= 0
 * - val is a pointer
 */
typedef struct ptr_hmap_pair_s {
  int32_t key;
  void *val;
} ptr_hmap_pair_t;

/*
 * Markers for empty/deleted pairs
 */
enum {
  PHMAP_DEL_KEY = -2,
  PHMAP_EMPTY_KEY = -1,
};

typedef struct ptr_hmap_s {
  ptr_hmap_pair_t *data;
  uint32_t size; // must be a power of 2
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} ptr_hmap_t;


/*
 * Default initial size
 */
#define PTR_HMAP_DEFAULT_SIZE 32
#define PTR_HMAP_MAX_SIZE (UINT32_MAX/8)

/*
 * Ratios: resize_threshold = size * RESIZE_RATIO
 *         cleanup_threshold = size * CLEANUP_RATIO
 */
#define PTR_HMAP_RESIZE_RATIO 0.6
#define PTR_HMAP_CLEANUP_RATIO 0.2


/*
 * Initialization:
 * - n = initial size, must be a power of 2
 * - if n = 0, the default size is used
 */
extern void init_ptr_hmap(ptr_hmap_t *hmap, uint32_t n);


/*
 * Delete: free memory
 */
extern void delete_ptr_hmap(ptr_hmap_t *hmap);


/*
 * Find record with key k. Return NULL if there's none
 */
extern ptr_hmap_pair_t *ptr_hmap_find(ptr_hmap_t *hmap, int32_t k);


/*
 * Get record with key k. If one is in the table return it.
 * Otherwise, add a fresh record with key k and value NULL and return it.
 */
extern ptr_hmap_pair_t *ptr_hmap_get(ptr_hmap_t *hmap, int32_t k);


/*
 * Erase record r
 */
extern void ptr_hmap_erase(ptr_hmap_t *hmap, ptr_hmap_pair_t *r);


/*
 * Remove all records
 */
extern void ptr_hmap_reset(ptr_hmap_t *hmap);


/*
 * Remove all records that satisfy f
 * - for every record r in the table, call f(aux, r)
 * - if that returns true, then the record r is deleted
 * - f must not have side effects
 */
typedef bool (*ptr_hmap_filter_t)(void *aux, const ptr_hmap_pair_t *r);

extern void ptr_hmap_remove_records(ptr_hmap_t *hmap, void *aux, ptr_hmap_filter_t f);



/*
 * Support for scanning all records:
 * - first gives the first non-null record in the table or NULL
 * - next(p) gives the next record after p or NULL
 * IMPORTANT: The hmap must not be modified between calls to next
 */
extern ptr_hmap_pair_t *ptr_hmap_first_record(ptr_hmap_t *hmap);
extern ptr_hmap_pair_t *ptr_hmap_next_record(ptr_hmap_t *hmap, ptr_hmap_pair_t *p);


#endif /* __PTR_HASH_MAP_H */
