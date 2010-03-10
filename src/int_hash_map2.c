/*
 * Maps pairs of 32bit integers to 32bit integers.
 * The keys must be non-negative.
 *
 * Supported oprations: addition/query/garbage collection.
 * Removal of individual records is not supported.
 */

#include <assert.h>

#include "memalloc.h"
#include "int_hash_map2.h"


/*
 * For degugging: check whether n is 0 or a power of 2
 */
#ifndef NDBEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif



/*
 * Initialization:
 * - n = initial size (must be 0 or a power of 2)
 * - if n = 0, the default size is used
 */
void init_int_hmap2(int_hmap2_t *hmap, uint32_t n) {
  int_hmap2_rec_t *tmp;
  uint32_t i;

  if (n == 0) {
    n = INT_HMAP2_DEF_SIZE;
  }

  if (n >= INT_HMAP2_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (int_hmap2_rec_t *) safe_malloc(n * sizeof(int_hmap2_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].k0 = INT_HMAP2_EMPTY;
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->resize_threshold = (uint32_t) (n * INT_HMAP2_RESIZE_RATIO);
}


/*
 * Free memory
 */
void delete_int_hmap2(int_hmap2_t *hmap) {
  safe_free(hmap->data);
  hmap->data = NULL;
}



/*
 * Hash a pair (k0, k1): Jenkins's hash.
 */

/* Jenkins's lookup3 code */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define final(a,b,c)      \
{                         \
  c ^= b; c -= rot(b,14); \
  a ^= c; a -= rot(c,11); \
  b ^= a; b -= rot(a,25); \
  c ^= b; c -= rot(b,16); \
  a ^= c; a -= rot(c,4);  \
  b ^= a; b -= rot(a,14); \
  c ^= b; c -= rot(b,24); \
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
 * Copy record d into a clean array
 * - data = array (its size must be 2^k for k>0)
 * - mask = 2^k-1
 * - data must not be full
 */
static void int_hmap2_clean_copy(int_hmap2_rec_t *data, int_hmap2_rec_t *r, uint32_t mask) {
  uint32_t j;

  j = hash_pair(r->k0, r->k1) & mask;
  while (data[j].k0 >= 0) {
    j ++;
    j &= mask;
  }
  data[j] = *r;
}



/*
 * Double the table size (keep the content).
 */
static void int_hmap2_extend(int_hmap2_t *hmap) {
  int_hmap2_rec_t *tmp, *r;
  uint32_t i, n, n2, mask;

  n = hmap->size;
  n2 = n<<1;
  if (n2 >= INT_HMAP2_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n2));

  tmp = (int_hmap2_rec_t *) safe_malloc(n2 * sizeof(int_hmap2_rec_t));
  for (i=0; i<n2; i++) {
    tmp[i].k0 = INT_HMAP2_EMPTY;
  }

  mask = n2 - 1;
  r = hmap->data;
  for (i=0; i<n; i++) {
    if (r->k0 >= 0) { // valid record
      int_hmap2_clean_copy(tmp, r, mask);      
    }
    r ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;

  hmap->resize_threshold = (uint32_t) (n2 * INT_HMAP2_RESIZE_RATIO);
}




/*
 * Find record with key (k0, kl)
 * - return NULL if that record is not in the table
 */
int_hmap2_rec_t *int_hmap2_find(int_hmap2_t *hmap, int32_t k0, int32_t k1) {
  int_hmap2_rec_t *r;
  uint32_t i, mask;

  assert(k0 >= 0 && k1 >= 0 && hmap->nelems < hmap->size);

  mask = hmap->size - 1;
  i = hash_pair(k0, k1) & mask;
  for (;;) {
    r = hmap->data + i;
    if (r->k0 < 0) return NULL;
    if (r->k0 == k0 && r->k1 == k1) return r;
    i ++;
    i &= mask;
  }
}




/*
 * Add record (k0, k1) to the table after resizing
 * - return a pointer to the new record
 */
static int_hmap2_rec_t *get_clean(int_hmap2_t *hmap, int32_t k0, int32_t k1) {
  uint32_t j, mask;

  mask = hmap->size - 1;
  j = hash_pair(k0, k1) & mask;
  while (hmap->data[j].k0 >= 0) {
    j ++;
    j &= mask;
  }

  hmap->data[j].k0 = k0;
  hmap->data[j].k1 = k1;

  return hmap->data + j;
}


/*
 * Get record with key (k0, k1).
 * - if one is in the table return it and set *new to false.
 * - otherwise, create a fresh record with key (k0, k1), and 
 *   set *new to false.
 * If a new record is created, val is not initialized.
 * - k0 and k2 must be non-negative.
 */
int_hmap2_rec_t *int_hmap2_get(int_hmap2_t *hmap, int32_t k0, int32_t k1, bool *new) {
  int_hmap2_rec_t *r;
  uint32_t i, mask;
  
  assert(k0 >= 0 && k1 >= 0 && hmap->nelems < hmap->size);

  *new = false;
  mask = hmap->size - 1;
  i = hash_pair(k0, k1) & mask;  
  for (;;) {
    r = hmap->data + i;
    if (r->k0 < 0) break;
    if (r->k0 == k0 && r->k1 == k1) return r;
    i ++;
    i &= mask;
  }

  /*
   * add new record in hmap->data
   */
  if (hmap->nelems >= hmap->resize_threshold) {
    // resize needed
    int_hmap2_extend(hmap);
    r = get_clean(hmap, k0, k1);
  } else {
    // add the new record in r
    r->k0 = k0;
    r->k1 = k1;
  }

  hmap->nelems ++;
  *new = true;

  return r;
}


/*
 * Empty the table
 */
void reset_int_hmap2(int_hmap2_t *hmap) {
  int_hmap2_rec_t *r;
  uint32_t i, n;

  r = hmap->data;
  n = hmap->size;
  for (i=0; i<n; i++) {
    r->k0 = INT_HMAP2_EMPTY;
    r ++;
  }

  hmap->nelems = 0;
}



/*
 * Garbage collection:
 * - we call f(aux, r) on every record r in hmap.
 * - if f returns true we keep r, otherwise we delete it.
 * We do this by copying the content into a new array, which
 * may be somewhat expensive if most records are kept.
 */
void int_hmap2_gc(int_hmap2_t *hmap, void *aux, keep_alive_fun_t f) {
  int_hmap2_rec_t *tmp, *r;
  uint32_t i, n, nelems, mask;
  
  n = hmap->size;
  tmp = (int_hmap2_rec_t *) safe_malloc(n * sizeof(int_hmap2_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].k0 = INT_HMAP2_EMPTY;
  }

  nelems = 0;    // number of elements kept
  mask = n - 1;
  r = hmap->data;  
  for (i=0; i<n; i++) {
    if (r->k0 >= 0 && f(aux, r)) {
      // keep r
      int_hmap2_clean_copy(tmp, r, mask);
      nelems ++;
    }
    r ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->nelems = nelems;
}
