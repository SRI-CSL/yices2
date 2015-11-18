/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * HASH MAP
 * keys are strings, values are 32 bit integers
 */

#ifndef __STRING_HASH_MAP_H
#define __STRING_HASH_MAP_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Records in the table:
 * - key = a string (with refcounter cf. refcount_string)
 * - hash = hash code of the key
 * - val = a 32 bit value
 */
typedef struct strmap_rec_s {
  char *key;
  uint32_t hash;
  int32_t val;
} strmap_rec_t;



/*
 * Table = array of 2^k records for some k
 * - nelems = number of records present (used)
 * - ndeleted = number of deleted records
 */
typedef struct strmap_s {
  strmap_rec_t *data;
  uint32_t size;
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} strmap_t;


#define STRMAP_DEF_SIZE 32
#define STRMAP_MAX_SIZE (UINT32_MAX/sizeof(strmap_rec_t))

#define STRMAP_RESIZE_RATIO  0.7
#define STRMAP_CLEANUP_RATIO  0.2


/*
 * Initialization:
 * - n = initial size. n must be a power of 2
 * - if n =0, the default is used
 */
extern void init_strmap(strmap_t *hmap, uint32_t n);


/*
 * Delete: free memory
 * - call decref on all the keys
 */
extern void delete_strmap(strmap_t *hmap);


/*
 * Reset: empty the table
 */
extern void reset_strmap(strmap_t *hmap);

/*
 * Find record with the given key.
 * Return NULL if there isn't one.
 *
 * NOTE: the returned pointer may become invalid after a call
 * to strmap_get or strmap_erase.
 */
extern strmap_rec_t *strmap_find(strmap_t *hmap, const char *key);


/*
 * Find or create a record with the given key
 * - if the table contains a record with that key,
 *   it's returned and is_new is set to  false.
 * - otherwise, a new record is added with the given key
 *   and value = 0. (A copy of the string key is made)
 *   In this case, is_new is set to true.
 *
 * The returned pointer may become invalid after the next call
 * to strmap_get or strmap_erase.
 */
extern strmap_rec_t *strmap_get(strmap_t *hmap, const char *key, bool *is_new);


/*
 * Remove record r:
 * - also call decref on r->key
 */
extern void strmap_erase(strmap_t *hmap, strmap_rec_t *r);


/*
 * Iterator: apply f(aux, r) to all records in the table
 * - aux is an arbitrary pointer
 * - f must not have side effects on the table
 */
typedef void (*strmap_iterator_t)(void *aux, strmap_rec_t *r);

extern void strmap_iterate(strmap_t *hmap, void *aux, strmap_iterator_t f);


#endif /* __STRING_HASH_MAP_H */
