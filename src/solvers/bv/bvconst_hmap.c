/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Hash table to store mapping from variables to bit-vector constants
 */

#include "utils/memalloc.h"
#include "terms/bv64_constants.h"
#include "terms/bv_constants.h"

#include "solvers/bv/bvconst_hmap.h"


/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialization:
 * - n = initial size, must be a power of 2
 * - if n = 0, the default size is used
 */
void init_bvconst_hmap(bvconst_hmap_t *hmap, uint32_t n) {
  bvconst_hmap_rec_t *tmp;
  uint32_t i;

  if (n == 0) {
    n = BVCONST_HMAP_DEFAULT_SIZE;
  }

  if (n >= BVCONST_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (bvconst_hmap_rec_t *) safe_malloc(n * sizeof(bvconst_hmap_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].key = BVCONST_HMAP_EMPTY_KEY;
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->resize_threshold = (uint32_t)(n * BVCONST_HMAP_RESIZE_RATIO);
}



/*
 * Free memory
 */
void delete_bvconst_hmap(bvconst_hmap_t *hmap) {
  bvconst_hmap_rec_t *tmp;
  uint32_t i, n, k;

  n = hmap->size;
  tmp = hmap->data;
  for (i=0; i<n; i++) {
    if (tmp->key >= 0 && tmp->nbits > 64) {
      k = (tmp->nbits + 31) >> 5;
      bvconst_free(tmp->val.p, k);
    }
    tmp ++;
  }
  safe_free(hmap->data);
  hmap->data = NULL;
}



/*
 * Empty the table
 */
void reset_bvconst_hmap(bvconst_hmap_t *hmap) {
  bvconst_hmap_rec_t *tmp;
  uint32_t i, n, k;

  n = hmap->size;
  tmp = hmap->data;
  for (i=0; i<n; i++) {
    if (tmp->key >= 0) {
      if (tmp->nbits > 64) {
        k = (tmp->nbits + 31) >> 5;
        bvconst_free(tmp->val.p, k);
      }
      tmp->key = BVCONST_HMAP_EMPTY_KEY;
    }
    tmp ++;
  }
  hmap->nelems = 0;
}



/*
 * Hash of a key (Jenkins hash)
 */
static uint32_t hash_key(int32_t k) {
  uint32_t x;

  x = (uint32_t) k;
  x = (x + 0x7ed55d16) + (x<<12);
  x = (x ^ 0xc761c23c) ^ (x>>19);
  x = (x + 0x165667b1) + (x<<5);
  x = (x + 0xd3a2646c) ^ (x<<9);
  x = (x + 0xfd7046c5) + (x<<3);
  x = (x ^ 0xb55a4f09) ^ (x>>16);

  return x;
}


/*
 * Make a copy of record d in a clean array data
 * - mask = size of data - 1 (size must be a power of 2)
 */
static void bvconst_hmap_clean_copy(bvconst_hmap_rec_t *data, bvconst_hmap_rec_t *d, uint32_t mask) {
  uint32_t j;

  j = hash_key(d->key) & mask;
  while (data[j].key >= 0) {
    j ++;
    j &= mask;
  }

  assert(data[j].key == BVCONST_HMAP_EMPTY_KEY);

  data[j] = *d;
}



/*
 * Make the table twice as large
 */
static void bvconst_hmap_extend(bvconst_hmap_t *hmap) {
  bvconst_hmap_rec_t *tmp, *d;
  uint32_t j, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 >= BVCONST_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (bvconst_hmap_rec_t *) safe_malloc(n2 * sizeof(bvconst_hmap_rec_t));
  for (j=0; j<n2; j++) {
    tmp[j].key = BVCONST_HMAP_EMPTY_KEY;
  }

  mask = n2 - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (d->key >= 0) {
      bvconst_hmap_clean_copy(tmp, d, mask);
    }
    d ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;
  hmap->resize_threshold = (uint32_t)(n2 * BVCONST_HMAP_RESIZE_RATIO);
}


/*
 * Find record with key k
 * - return NULL if k is not in the table
 */
bvconst_hmap_rec_t *bvconst_hmap_find(bvconst_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  bvconst_hmap_rec_t *d;

  assert(k >= 0 && hmap->size > hmap->nelems);

  mask = hmap->size - 1;
  j = hash_key(k) & mask;
  for (;;) {
    d = hmap->data + j;
    if (d->key == k) return d;
    if (d->key < 0) return NULL;
    j ++;
    j &= mask;
  }
}


/*
 * Find or add record with key k
 * - if a new record is created, it's initialize with key = k, nbits = 0, val = 0
 */
static bvconst_hmap_rec_t *bvconst_hmap_get(bvconst_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  bvconst_hmap_rec_t *d;

  assert(k >= 0 && hmap->size > hmap->nelems);

  mask = hmap->size - 1;
  j = hash_key(k) & mask;

  for (;;) {
    d = hmap->data + j;
    if (d->key == k) return d;
    if (d->key < 0) break;
    j ++;
    j &= mask;
  }


  /*
   * store new record in d
   */
  d->key = k;
  d->nbits = 0;
  d->val.c = 0;

  return d;
}


/*
 * Assign c as value of x
 */
void bvconst_hmap_set_val64(bvconst_hmap_t *hmap, int32_t x, uint64_t c, uint32_t n) {
  bvconst_hmap_rec_t *r;
  uint32_t old_k;

  assert(0 <= x && 1 <= n && n <= 64);

  r = bvconst_hmap_get(hmap, x);
  assert(r->key == x);

  if (r->nbits == 0) {
    // new record
    r->nbits = n;
    r->val.c = norm64(c, n);

    hmap->nelems ++;
    if (hmap->nelems >= hmap->resize_threshold) {
      bvconst_hmap_extend(hmap);
    }
  } else {
    if (r->nbits > 64) {
      old_k = (r->nbits + 31) >> 5;
      bvconst_free(r->val.p, old_k);
    }
    r->nbits = n;
    r->val.c = norm64(c, n);
  }
}


void bvconst_hmap_set_val(bvconst_hmap_t *hmap, int32_t x, uint32_t *c, uint32_t n) {
  bvconst_hmap_rec_t *r;
  uint32_t k, old_k;

  assert(0 <= x && 64 < n);

  k = (n + 31) >> 5;
  r = bvconst_hmap_get(hmap, x);
  assert(r->key == x);

  if (r->nbits == 0) {
    // new record
    r->nbits = n;
    r->val.p = bvconst_alloc(k);
    bvconst_set(r->val.p, k, c);
    bvconst_normalize(r->val.p, n);

    hmap->nelems ++;
    if (hmap->nelems >= hmap->resize_threshold) {
      bvconst_hmap_extend(hmap);
    }
  } else {
    old_k = (r->nbits + 31) >> 5;
    if (old_k != k) {
      if (r->nbits > 64) bvconst_free(r->val.p, old_k);
      r->val.p = bvconst_alloc(k);
    }

    r->nbits = n;
    bvconst_set(r->val.p, k, c);
    bvconst_normalize(r->val.p, n);
  }
}
