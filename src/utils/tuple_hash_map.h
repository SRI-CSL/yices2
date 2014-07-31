/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * MAPS TUPLES (ARRAYS) OF 32BIT INTEGERS TO 32BIT INTEGERS
 */

#ifndef __TUPLE_HASH_MAP_H
#define __TUPLE_HASH_MAP_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Records stored in the table
 * - key = array of n signed 32bit integers (n = arity)
 * - val = signed 32bit integers
 * - hash = unsigned 32bit integer
 */
typedef struct tuple_hmap_rec_s {
  uint32_t hash;
  uint32_t arity;
  int32_t value;
  int32_t key[0]; // real size = arity
} tuple_hmap_rec_t;


/*
 * Maximal number of elements in key
 */
#define TUPLE_HMAP_MAX_ARITY ((UINT32_MAX-sizeof(tuple_hmap_rec_t))/sizeof(int32_t))


/*
 * Markers for deleted elements in the table
 */
#define TUPLE_HMAP_DELETED ((tuple_hmap_rec_t *) 1)


/*
 * Hash table
 */
typedef struct tuple_hmap_s {
  tuple_hmap_rec_t **data;
  uint32_t size;               // size of data array, must be a power of two
  uint32_t nelems;             // number of elements stored
  uint32_t ndeleted;           // number of records marked as deleted
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} tuple_hmap_t;


/*
 * Default size
 */
#define TUPLE_HMAP_DEF_SIZE 32
#define TUPLE_HMAP_MAX_SIZE (UINT32_MAX/8)


/*
 * Ratios: resize_threshold = size * RESIZE_RATIO
 *         cleanup_threshold = size * CLEANUP_RATIO
 */
#define TUPLE_HMAP_RESIZE_RATIO 0.6
#define TUPLE_HMAP_CLEANUP_RATIO 0.2


/*
 * Initialization:
 * - n = initial size of the table. n must be 0 or a power of 2
 * - if n = 0, the default size is used.
 */
extern void init_tuple_hmap(tuple_hmap_t *hmap, uint32_t n);


/*
 * Deletion: free all memory used by the table
 */
extern void delete_tuple_hmap(tuple_hmap_t *hmap);


/*
 * Remove all records
 */
extern void reset_tuple_hmap(tuple_hmap_t *hmap);




/*
 * Find record that matches the given key
 * - key must be an array of n integers
 * - n must be no more than TUPLE_HMAP_MAX_ARITY
 * - return NULL if there's no matching record
 */
extern tuple_hmap_rec_t *tuple_hmap_find(tuple_hmap_t *hmap, uint32_t n, int32_t key[]);


/*
 * Get a record for the given key
 * - key must be an array of n integers
 * - n must be no more than TUPLE_HMAP_MAX_ARITY
 * - if there's a matching record in the table, it's returned and *new is set to false.
 * - otherwise, a new record is created and added to the table, *new is set to true,
 *   and the new record is returned.
 *   The value field of the new record is not initialized.
 */
extern tuple_hmap_rec_t *tuple_hmap_get(tuple_hmap_t *hmap, uint32_t n, int32_t key[], bool *new);


/*
 * Add the record (key, val) to the table
 * - key must be an array of n integers
 * - n must be no more than TUPLE_HMAP_MAX_ARITY
 * - there must not be a record with the same key in the table.
 */
extern void tuple_hmap_add(tuple_hmap_t *hmap, uint32_t n, int32_t key[], int32_t val);


/*
 * Remove record r from the table:
 * This also frees r, so r is not usable after this function is called.
 */
extern void tuple_hmap_erase(tuple_hmap_t *hmap, tuple_hmap_rec_t *r);


/*
 * Remove record that matches the given key
 * - key must be an array of n integers
 * - n must be no more than TUPLE_HMAP_MAX_ARITY
 * - no change if there's no matching record in the table.
 */
extern void tuple_hmap_remove(tuple_hmap_t *hmap, uint32_t n, int32_t key[]);


/*
 * Garbage collection
 * - f must be a function that indicates whether a record should be kept or not
 * - aux is an auxiliary pointer passed as argument to f
 * The function scans the hash tabe and calls f(aux, r) for every record r
 * in the table. If f returns false, r is deleted, otherwise, r is kept.
 */
typedef bool (*tuple_hmap_keep_fun_t)(void *aux, tuple_hmap_rec_t *r);

extern void tuple_hmap_gc(tuple_hmap_t *hmap, void *aux, tuple_hmap_keep_fun_t f);



#endif /* __TUPLE_HASH_MAP_H */
