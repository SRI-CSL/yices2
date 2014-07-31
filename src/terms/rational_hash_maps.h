/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Hash table that maps pairs of rationals to non-negative integers.
 *
 * This is intended to be used in the simplex model construction.
 * For an extended rational q = a + b\delta, the table keeps track
 * of the number of simplex variables whose value is equal to q.
 */

#ifndef __RATIONAL_HASH_MAPS_H
#define __RATIONAL_HASH_MAPS_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/extended_rationals.h"


/*
 * Records stored in the table:
 * - key is an extended rational
 * - value is an integer
 * The record is empty if value = 0 (then key is zero)
 * The record is deleted if value = UINT32_MAX (then key is zero too)
 */
typedef struct xq_hmap_rec_s {
  uint32_t value;
  xrational_t key;
} xq_hmap_rec_t;



/*
 * Hash table proper:
 * - size = size of the data array. It's always a power of 2.
 * - nelems = number of elements in the table
 *          = number of records whose value is positive
 * - ndeleted = number of elements marked as deleted
 * - nentries = total number of elements added to the table
 * - resize_threshold = RESIZE_RATIO * size.
 *   When nelems >= resize_threshold, the table size if doubled.
 * - cleanup_threshold = CLEANUP_RATIO * size
 *   When ndeleted >= cleanup_threshold, the deleted elements are removed.
 */
typedef struct xq_hmap_s {
  xq_hmap_rec_t *data;
  uint32_t size;
  uint32_t nelems;
  uint32_t nentries;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} xq_hmap_t;


#define XQ_HMAP_DEFAULT_SIZE 32
#define XQ_HMAP_MAX_SIZE (UINT32_MAX/sizeof(xq_hmap_rec_t))

#define XQ_HMAP_RESIZE_RATIO  0.6
#define XQ_HMAP_CLEANUP_RATIO 0.2


/*
 * Initialization
 * - n = initial size
 * - n must be 0 or a power of two
 * - if n = 0, then the default size is used.
 */
extern void init_xq_hmap(xq_hmap_t *hmap, uint32_t n);


/*
 * Delete: free all memory used by hmap
 * - also frees all the rationals
 */
extern void delete_xq_hmap(xq_hmap_t *hmap);


/*
 * Reset: empty the map
 */
extern void reset_xq_hmap(xq_hmap_t *hmap);


/*
 * Copy the content of hmap2 into hmap1:
 * - hmap1 must be initialized
 * - hmap1 is reset first
 */
extern void copy_xq_hmap(xq_hmap_t *hmap1, xq_hmap_t *hmap2);


/*
 * Add an entry of key = q:
 * - if there's already a record with key q then increment
 *   its value by 1
 * - otherwise, create a new record with key q and value = 1
 * - this increments hmap->nentries
 * - if a new record is created, hmap->nelems is also incremented
 */
extern void xq_hmap_add_entry(xq_hmap_t *hmap, xrational_t *q);


/*
 * Remove an entry of key q
 * - there must be a record in the hash table with that key
 * - the value of that record is decremented and the record is
 *   deleted if the value becomes 0.
 */
extern void xq_hmap_remove_entry(xq_hmap_t *hmap, xrational_t *q);


/*
 * Shift entry q by delta
 * - q must be present in the table.
 * - this removes one entry for q and add one entry for (q + delta)
 */
extern void xq_hmap_shift_entry(xq_hmap_t *hmap, xrational_t *q, rational_t *delta);


/*
 * Shift variants
 * addmul: replace entry q by (q + a * delta)
 * submul: replace entry q by (q - a * delta)
 */
extern void xq_hmap_addmul_entry(xq_hmap_t *hmap, xrational_t *q, rational_t *a, rational_t *delta);
extern void xq_hmap_submul_entry(xq_hmap_t *hmap, xrational_t *q, rational_t *a, rational_t *delta);



/*
 * Return the value attached to q in the table
 * or 0 if there's no record with entry q.
 */
extern uint32_t xq_hmap_multiplicity(xq_hmap_t *hmap, xrational_t *q);


/*
 * Test whether q is present in the table
 * - return true if there's a record of key q in the table
 * - return false otherwise
 */
static inline bool xq_hmap_has_entry(xq_hmap_t *hmap, xrational_t *q) {
  return xq_hmap_multiplicity(hmap, q) > 0;
}



/*
 * Get the number of entries
 */
static inline uint32_t xq_hmap_num_entries(xq_hmap_t *hmap) {
  return hmap->nentries;
}


/*
 * Get the number of classes = number of distinct records
 */
static inline uint32_t xq_hmap_num_classes(xq_hmap_t *hmap) {
  return hmap->nelems;
}



#endif /* __RATIONAL_HASH_MAPS_H */
