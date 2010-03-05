/*
 * Maps 32bit integers to 32bit integers (both signed)
 * Assumes that keys and values are non-negative
 */

#ifndef __INT_HASH_MAP_H
#define __INT_HASH_MAP_H

#include <stdint.h>

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
 * - n = initial size, must be a power of 2
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
extern int_hmap_pair_t *int_hmap_find(int_hmap_t *hmap, int32_t k);

/*
 * Get record with key k. If one is in the table return it.
 * Otherwise, add a fresh record with key k and value -1 and return it.
 */
extern int_hmap_pair_t *int_hmap_get(int_hmap_t *hmap, int32_t k);

/*
 * Erase record r
 */
extern void int_hmap_erase(int_hmap_t *hmap, int_hmap_pair_t *r);

/*
 * Remove all records
 */
extern void int_hmap_reset(int_hmap_t *hmap);


/*
 * Support for scanning all records:
 * - first gives the first non-null record in the table or NULL
 * - next(p) gives the next record after p or NULL
 * IMPORTANT: The hmap must not be modified between calls to next
 */
extern int_hmap_pair_t *int_hmap_first_record(int_hmap_t *hmap);
extern int_hmap_pair_t *int_hmap_next_record(int_hmap_t *hmap, int_hmap_pair_t *p);


#endif /* __INT_HASH_MAP_H */
