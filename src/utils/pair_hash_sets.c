/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * HASH SETS FOR PAIRS OF NON-NEGATIVE INTEGERS
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/pair_hash_sets.h"

/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialize
 * - n = initial size. n must be a power of 2
 * - if n is 0, the default size is used
 */
void init_pair_hset(pair_hset_t *set, uint32_t n) {
  int_pair_t *tmp;
  uint32_t i;

  if (n == 0) {
    n = PAIR_HSET_DEFAULT_SIZE;
  }

  if (n >= PAIR_HSET_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (int_pair_t *) safe_malloc(n * sizeof(int_pair_t));
  for (i=0; i<n; i++) {
    tmp[i].left = -1;
  }

  set->data = tmp;
  set->size = n;
  set->nelems = 0;
  set->resize_threshold = (uint32_t)(PAIR_HSET_RESIZE_RATIO * n);
}


/*
 * Delete: free memory
 */
void delete_pair_hset(pair_hset_t *set) {
  safe_free(set->data);
  set->data = NULL;
}




/*
 * Hash of a pair k0, k1 based on Jenkins lookup3 code.
 * (public domain code, see http://www.burtleburtle.net)
 */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define final(x,y,z)      \
{                         \
  z ^= y; z -= rot(y,14); \
  x ^= z; x -= rot(z,11); \
  y ^= x; y -= rot(x,25); \
  z ^= y; z -= rot(y,16); \
  x ^= z; x -= rot(z,4);  \
  y ^= x; y -= rot(x,14); \
  z ^= y; z -= rot(y,24); \
}

static uint32_t hash_pair(int32_t k0, int32_t k1) {
  uint32_t x, y, z;

  x = (uint32_t) k0;
  y = (uint32_t) k1;
  z = 0xdeadbeef;
  final(x, y, z);

  return z;
}


/*
 * Check whether the pair <x, y> is present
 */
bool pair_hset_member(pair_hset_t *set, int32_t x, int32_t y) {
  uint32_t i, mask;
  int_pair_t *d;

  assert(x >= 0 && y >= 0 && set->nelems < set->size);

  mask = set->size - 1;
  d = set->data;
  i = hash_pair(x, y) & mask;
  for (;;) {
    if (d[i].left < 0) return false;
    if (d[i].left == x && d[i].right == y) return true;
    i ++;
    i &= mask;
  }
}


/*
 * Copy pair *p into array data.
 * - size of array data must be a power of 2
 * - mask = size of data - 1
 * - p must be a valid pair: p->left >= 0, p->right >= 0.
 * - data must be a clean array: empty slots must be marked by setting left to
 *   a negative value
 * - there must be some empty slot in data
 */
static void pair_hset_clean_copy(int_pair_t *data, int_pair_t *p, uint32_t mask) {
  uint32_t i;

  i = hash_pair(p->left, p->right) & mask;
  while (data[i].left >= 0) {
    i ++;
    i &= mask;
  }
  data[i] = *p;
}


/*
 * Extend: make set twice as large. Keep all the elements
 */
static void pair_hset_extend(pair_hset_t *set) {
  uint32_t n, n2;
  int_pair_t *tmp, *r;
  uint32_t i, mask;

  n = set->size;
  n2 = n << 1;
  if (n2 >= PAIR_HSET_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (int_pair_t *) safe_malloc(n2 * sizeof(int_pair_t));
  for (i=0; i<n2; i++) {
    tmp[i].left = -1;
  }

  mask = n2 - 1;
  r = set->data;
  for (i=0; i<n; i++) {
    if (r->left >= 0) {
      pair_hset_clean_copy(tmp, r, mask);
    }
    r ++;
  }

  safe_free(set->data);
  set->data = tmp;
  set->size = n2;
  set->resize_threshold = (uint32_t) (n2 * PAIR_HSET_RESIZE_RATIO);
}


/*
 * Add pair <x, y> to set
 * - return true if it's not already there
 * - return false if it's already in the set
 */
bool pair_hset_add(pair_hset_t *set, int32_t x, int32_t y) {
  uint32_t i, mask;
  int_pair_t *d;

  assert(x >= 0 && y >= 0 && set->nelems < set->size);

  mask = set->size - 1;
  d = set->data;
  i = hash_pair(x, y) & mask;
  while (d[i].left >= 0) {
    if (d[i].left == x && d[i].right == y) return false;
    i ++;
    i &= mask;
  }

  d[i].left = x;
  d[i].right = y;
  set->nelems ++;
  if (set->nelems > set->resize_threshold) {
    pair_hset_extend(set);
  }

  return true;
}



/*
 * Empty the set
 */
void pair_hset_reset(pair_hset_t *set) {
  uint32_t i, n;

  n = set->size;
  for (i=0; i<n; i++) {
    set->data[i].left = -1;
  }
  set->nelems = 0;
}
