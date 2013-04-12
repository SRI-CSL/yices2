/*
 * Hash map: keys are strings, values are 32 bit integers
 */

#include <assert.h>
#include <string.h>

#include "memalloc.h"
#include "refcount_strings.h"
#include "hash_functions.h"
#include "string_hash_map.h"


/*
 * For debugging: check whether n is a power of 2 (or n == 0)
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialization:
 * - n = initial size (must be a power of 2)
 * - if n = 0, the default size is used
 */
void init_strmap(strmap_t *hmap, uint32_t n) {
  strmap_rec_t *tmp;
  uint32_t i;

  if (n == 0) {
    n = STRMAP_DEF_SIZE;
  }

  if (n >= STRMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));
  tmp = (strmap_rec_t *) safe_malloc(n * sizeof(strmap_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].key = NULL;
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t) (n * STRMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n * STRMAP_CLEANUP_RATIO);
}


/*
 * Check whether key is valid (i.e., not NULL or DELETED_KEY)
 */
#define MASK_TAG ((size_t) 3)

static inline bool valid_key(const char *key) {
  return (((size_t) key) & ~MASK_TAG) != ((size_t) NULL);
}


/*
 * Delete: call decref on all keys
 */
void delete_strmap(strmap_t *hmap) {
  uint32_t i, n;
  char *key;

  n = hmap->size;
  for (i=0; i<n; i++) {
    key = hmap->data[i].key;
    if (valid_key(key)) {
      string_decref(key);
    }
  }

  safe_free(hmap->data);
  hmap->data = NULL;
}


