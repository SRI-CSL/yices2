/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * UNION-FIND DATA STRUCTURE FOR SETS OF NON-NEGATIVE INTEGERS
 */

#include <stdint.h>
#include <assert.h>

#include "utils/memalloc.h"
#include "utils/union_find.h"


/*
 * Initialization:
 * - n = initial size
 * If n = 0, nothing is allocated, arrays of default size are allocated
 * on the first addition.
 */
void init_partition(partition_t *p, uint32_t n) {
  if (n >= MAX_PARTITION_SIZE) {
    out_of_memory();
  }

  p->size = n;
  p->nelems = 0;
  if (n == 0) {
    p->parent = NULL;
    p->rank = NULL;
  } else {
    p->parent = (int32_t *) safe_malloc(n * sizeof(int32_t));
    p->rank = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  }
}


/*
 * Delete: free arrays parent and rank
 */
void delete_partition(partition_t *p) {
  safe_free(p->parent);
  safe_free(p->rank);
  p->parent = NULL;
  p->rank = NULL;
}



/*
 * Resize: make sure arrays are large enough for adding element x
 * and initialize parents[y] to -1 for y = p->nelems to x
 * - do nothing if n < p->nelems;
 */
static void resize_partition(partition_t *p, int32_t x) {
  uint32_t n;
  int32_t i;

  n = p->size;
  if (n <= x) {
    if (n == 0) {
      n = DEF_PARTITION_SIZE;
    } else {
      n += n>>1; // try to increase by 50%
    }
    if (n <= x) {
      n = x+1;
    }
    if (n >= MAX_PARTITION_SIZE) {
      out_of_memory();
    }

    p->size = n;
    p->parent = (int32_t *) safe_realloc(p->parent, n * sizeof(int32_t));
    p->rank = (uint8_t *) safe_realloc(p->rank, n * sizeof(uint8_t));
  }

  assert(x < p->size);

  for (i=p->nelems; i<=x; i++) {
    p->parent[i] = -1;
  }
  p->nelems = i;
}



/*
 * Add x to the partition in a singleton class
 * - x must be non-negative and not present
 */
void partition_add(partition_t *p, int32_t x) {
  if (x >= p->nelems) {
    resize_partition(p, x);
  }
  assert(p->parent[x] == -1);
  p->parent[x] = x;
  p->rank[x] = 0;
}


/*
 * Add x to the partition in a singleton class and make
 * sure x will remain root of its class
 * - x must be non-negative and not present
 */
void partition_add_root(partition_t *p, int32_t x) {
  if (x >= p->nelems) {
    resize_partition(p, x);
  }
  assert(p->parent[x] == -1);
  p->parent[x] = x;
  p->rank[x] = 255;
}


/*
 * Find the root of x's class
 * - return -1 if x has not been added to any class
 */
int32_t partition_find(partition_t *p, int32_t x) {
  int32_t y, r;
  int32_t *parent;

  if (x >= p->nelems) return -1;

  parent = p->parent;
  y = parent[x];
  if (y < 0 || y == x) return y;

  // find the root r
  for (;;) {
    r = parent[y];
    if (r == y) break;
    y = r;
  }

  // path compression, starting from x
  do {
    y = parent[x];
    parent[x] = r;
    x = y;
  } while (x != r);

  return r;
}



/*
 * Merge the classes of x and y
 * - both must be root of their class (and the classes must be distinct)
 * - both must not both have rank 255
 */
void partition_merge(partition_t *p, int32_t x, int32_t y) {
  uint8_t r_x, r_y;

  assert(partition_is_root(p, x) && partition_is_root(p, y) && x != y);

  r_x = p->rank[x];
  r_y = p->rank[y];

  assert(r_x != 255 || r_y != 255);

  if (r_x < r_y) {
    p->parent[x] = y;
  } else {
    p->parent[y] = x;
    if (r_x == r_y) {
      p->rank[x] = r_x + 1;
    }
  }
}
