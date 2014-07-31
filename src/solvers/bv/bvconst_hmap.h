/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Hash map to store the bitvector constant value
 * mapped to bitvector variables.
 * - keys are non-negative 32bit integers
 * - values are either 64bit unsigned integers or pointers to
 *   arrays of uint32_t words
 * - there's no support for deleting records (except full reset)
 *
 * Bitvector constants are allocated using functions from bv_constants
 * so make sure init_bvconstants is called before using this module.
 */

#ifndef __BVCONST_HMAP_H
#define __BVCONST_HMAP_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>


/*
 * Records:
 * - key is a 32bit signed integer
 * - nbits = number of bits in value
 * - val is a union
 */
typedef struct bvconst_hmap_rec_s {
  int32_t key;
  uint32_t nbits;
  union {
    uint64_t c;
    uint32_t *p;
  } val;
} bvconst_hmap_rec_t;


/*
 * Marker for empty records
 */
enum {
  BVCONST_HMAP_EMPTY_KEY = -1,
};


/*
 * Hash table: size must be a power of 2
 */
typedef struct bvconst_hmap_s {
  bvconst_hmap_rec_t *data;
  uint32_t size;
  uint32_t nelems;
  uint32_t resize_threshold;
} bvconst_hmap_t;


#define BVCONST_HMAP_DEFAULT_SIZE 64
#define BVCONST_HMAP_MAX_SIZE (UINT32_MAX/sizeof(bvconst_hmap_rec_t))

#define BVCONST_HMAP_RESIZE_RATIO 0.6


/*
 * Initialization:
 * - n = initial size (must be a power of 2)
 * - if n = 0, the default size is used
 */
extern void init_bvconst_hmap(bvconst_hmap_t *hmap, uint32_t n);


/*
 * Delete: make sure the pointers are freed first
 * (i.e. finalize using hmap_iterate)
 */
extern void delete_bvconst_hmap(bvconst_hmap_t *hmap);


/*
 * Reset: empty the table
 */
extern void reset_bvconst_hmap(bvconst_hmap_t *hmap);


/*
 * Assign value c to x (no more than 64bit)
 * - x must be non-negative
 * - n = number of bits (must be between 1 and 64)
 * - c is normalized then copied as value of x
 *
 * If x has a pointer value before (i.e., more than 64bits),
 * that valued is freed.
 */
extern void bvconst_hmap_set_val64(bvconst_hmap_t *hmap, int32_t x, uint64_t c, uint32_t n);


/*
 * Assign a value of more than 64bits to c
 * - x must be non-negative
 * - n = number of bits (must be more than 64)
 * - c must point to an array of k words, where k = ceil(n/32).
 * - a copy of c is made internally then it's normalized modulo 2^n
 */
extern void bvconst_hmap_set_val(bvconst_hmap_t *hmap, int32_t x, uint32_t *c, uint32_t n);



/*
 * Find record with key k: return NULL if it's not present
 * - k must be non-negative
 *
 * Important: if r = bvconst_hmap_find(hmap, k) then r is a pointer
 * inside hmap->data. It may become invalid it new records are added
 * to the table.
 */
extern bvconst_hmap_rec_t *bvconst_hmap_find(bvconst_hmap_t *hmap, int32_t k);


/*
 * Check whether k is present in the table
 */
static inline bool bvconst_hmap_key_is_present(bvconst_hmap_t *hmap, int32_t k) {
  return bvconst_hmap_find(hmap, k) != NULL;
}


/*
 * Get the 64bit value mapped to k
 * - k must be present and have a 64bit value
 */
static inline uint64_t bvconst_hmap_get_val64(bvconst_hmap_t *hmap, int32_t k) {
  bvconst_hmap_rec_t *r;

  r = bvconst_hmap_find(hmap, k);
  assert(r != NULL && r->nbits <= 64 && r->key == k);
  return r->val.c;
}


/*
 * Get the value mapped to k (more than 64bits)
 * - k must be present
 * - the value is an array of 32bit words (cf. bv_constants.h)
 */
static inline uint32_t *bvconst_hmap_get_val(bvconst_hmap_t *hmap, int32_t k) {
  bvconst_hmap_rec_t *r;

  r = bvconst_hmap_find(hmap, k);
  assert(r != NULL && r->nbits > 64 && r->key == k);
  return r->val.p;
}


#endif /* __BVCONST_HMAP_H */
