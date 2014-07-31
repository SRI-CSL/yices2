/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * UNION-FIND DATA STRUCTURE FOR SETS OF NON-NEGATIVE INTEGERS
 */

#ifndef __UNION_FIND_H
#define __UNION_FIND_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>


/*
 * Each item is a non-negative integer (e.g., a term index)
 * For item i, we need
 * - parent[i] = an item index (32bit)
 * - rank[i] = 8bit
 * If x is not present in any set, we set
 * - parent[i] = -1
 * For a root term i, we have parent[i] == i, and rank[i] is
 * close to the log of the size of its class. Since each class
 * has size >= 2^rank[root], 8bits are more than enough.
 *
 * Some items can be marked so that they always stay root of their
 * classes. This is done by setting their rank to 255. Two classes
 * whose roots have rank 255 cannot be merged.
 *
 * Other components:
 * - size = size of arrays parent and rank
 * - nelems = index of the largest element added + 1
 */
typedef struct partition_s {
  uint32_t nelems;
  uint32_t size;
  int32_t *parent;
  uint8_t *rank;
} partition_t;

#define DEF_PARTITION_SIZE 100
#define MAX_PARTITION_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Initialization:
 * - n = initial size
 * If n = 0, nothing is allocated, arrays of default size are allocated
 * on the first addition.
 */
extern void init_partition(partition_t *p, uint32_t n);


/*
 * Delete: free memory
 */
extern void delete_partition(partition_t *p);


/*
 * Reset: empty
 */
static inline void reset_partition(partition_t *p) {
  p->nelems = 0;
}


/*
 * Add element x (to a new singleton class)
 * - x must be non-negative
 * - x must not be present already.
 */
extern void partition_add(partition_t *p, int32_t x);


/*
 * Add x as a forced root and build singleton class
 * - x must be non-negative
 * - x must not be present already.
 */
extern void partition_add_root(partition_t *p, int32_t x);

/*
 * Find the representative of x
 * - return -1 if x is not present
 */
extern int32_t partition_find(partition_t *p, int32_t x);

/*
 * Check whether x is a root
 */
static inline bool partition_is_root(partition_t *p, int32_t x) {
  assert(x >= 0);
  return x < p->nelems && p->parent[x] == x;
}

/*
 * Merge the classes of x and y
 * - x and y must be distinct roots
 * - x and y must not both be marked as forced roots
 */
extern void partition_merge(partition_t *p, int32_t x, int32_t y);



#endif /* __UNION_FIND_H */
