/*
 * Sets of integers stored as arrays
 * Support for hash consing
 */

#ifndef __VSETS_H
#define __VSETS_H

#include <stdint.h>


/*
 * Set descriptor:
 * - hash = hash code
 * - nelems = number of elements
 * - data = array of elements, sorted in increasing order
 */
typedef struct vset_s {
  uint32_t hash;
  uint32_t nelems;
  int32_t data[0]; // real size = nelems
} vset_t;

#define MAX_VSET_SIZE ((UINT32_MAX-sizeof(vset_t))/sizeof(int32_t))


/*
 * Table of sets for hash consing
 */
typedef struct vset_htbl_s {
  vset_t **data;
  uint32_t size;
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} vset_htbl_t;


/*
 * Default and max size
 */
#define DEF_VSET_HTBL_SIZE 64
#define MAX_VSET_HTBL_SIZE (UINT32_MAX/sizeof(vset_t*))

/*
 * Ratios: resize_threshold = size * RESIZE_RATIO
 *         cleanup_threshold = size * CLEANUP_RATIO
 */
#define VSET_HTBL_RESIZE_RATIO 0.6
#define VSET_HTBL_CLEANUP_RATIO 0.2

/*
 * Marker for deleted sets
 */
#define DELETED_VSET ((vset_t *) 1)


/*
 * Initialize table
 * - n = initial size: must be a power of 2
 * - if n = 0 the default size is used
 */
extern void init_vset_htbl(vset_htbl_t *tbl, uint32_t n);

/*
 * Delete
 */
extern void delete_vset_htbl(vset_htbl_t *tbl);


/*
 * Empty the table
 */
extern void reset_vset_htbl(vset_htbl_t *tbl);


/*
 * Find set a[0 .. n-1]
 * - a[0 ... n-1] must be an array of n elements sorted in increasing
 *   order
 * - return NULL if the set is not in the table
 */
extern vset_t *vset_htbl_find(vset_htbl_t *tbl, uint32_t n, int32_t *a);

/*
 * Get set a[0 ... n-1]. Create it if it's not in table already.
 */
extern vset_t *vset_htbl_get(vset_htbl_t *tbl, uint32_t n, int32_t *a);


/*
 * Remove set a[0...n-1] from the table
 * - no change if the set is not present
 */
extern void vset_htbl_remove(vset_htbl_t *tbl, uint32_t n, int32_t *a);



#endif /* __VSETS_H */
