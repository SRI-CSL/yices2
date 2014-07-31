/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Hash-table to cache the lower and upper bounds on a variable x.
 *
 * Each value stored in the cache is a record that stores a lower
 * and upper bound on a variable x. There are two possible records
 * depending on whether x is interpreted as a signed (2's complement)
 * or unsigned integer.
 *
 * Each record contains:
 * - header: encodes variable x + one bit to indicate whether it's
 *   signed or unsigned
 * - bitsize = number of bits in x
 * - data = an array of 2*w 32bit words that stores the lower
 *          and upper bounds
 *   w is equal to ceil(bitsize/32)
 *   data[0 .. w-1]    = lower bound (little endian)
 *   data[w .. 2w - 1] = upper bound
 */

#ifndef __BVBOUND_CACHE_H
#define __BVBOUND_CACHE_H

#include <stdint.h>
#include <assert.h>


/*
 * Records stored in the table
 */
typedef struct bvbound_s {
  uint32_t header;
  uint32_t bitsize;
  uint32_t data[0]; // real size = 2 * ceil(bitsize/32)
} bvbound_t;



/*
 * Flag to specify either signed/unsigned bound
 */
typedef enum bvbound_tag {
  BVBOUND_UNSIGNED, // 0
  BVBOUND_SIGNED,   // 1
} bvbound_tag_t;


/*
 * Header format:
 * - low-order bit = 0: unsigned bound
 *   low-order bit = 1: signed
 * - bit 31 to 1 store the variable
 */
static inline uint32_t bvbound_header(int32_t x, bvbound_tag_t tag) {
  assert(x >= 0 && (((uint32_t) tag) & ~((uint32_t) 1)) == 0);
  return (((uint32_t) x) << 1) | ((uint32_t) tag);
}

static inline int32_t bvbound_header_var(uint32_t h) {
  return (int32_t) (h >> 1);
}

static inline bvbound_tag_t bvbound_header_tag(uint32_t h) {
  return (bvbound_tag_t) (h & 1);
}





/*
 * Cache: (similar to int_hash_table, etc.)
 */
typedef struct bvbound_cache_s {
  bvbound_t **data;    // hash-table proper
  uint32_t size;      // size of data (must be a power of 2)
  uint32_t nelems;    // number of elements
  uint32_t ndeleted;  // number of deleted elements
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} bvbound_cache_t;


/*
 * Marker for deleted elements.
 * The empty slots contains NULL.
 */
#define DELETED_BVBOUND ((bvbound_t *) 1)


/*
 * Default sizes and thresholds
 */
#define DEF_BVBOUND_CACHE_SIZE  32
#define MAX_BVBOUND_CACHE_SIZE  (UINT32_MAX/sizeof(bvbound_t *))

#define BVBOUND_CACHE_RESIZE_RATIO  0.7
#define BVBOUND_CACHE_CLEANUP_RATIO 0.2




/************************
 *  CREATION/DELETION   *
 ***********************/

/*
 * Initialize cache with size = n
 * - n must be a power of two
 * - if n = 0, the default size is used.
 */
extern void init_bvbound_cache(bvbound_cache_t *cache, uint32_t n);


/*
 * Delete cache: all the data it contains is freed
 */
extern void delete_bvbound_cache(bvbound_cache_t *cache);


/*
 * Reset cache: empty it
 */
extern void reset_bvbound_cache(bvbound_cache_t *cache);



/**************************
 *  ACCESS TO COMPONENTS  *
 *************************/

static inline int32_t bvbound_var(bvbound_t *b) {
  return bvbound_header_var(b->header);
}

static inline bvbound_tag_t bvbound_type(bvbound_t *b) {
  return bvbound_header_tag(b->header);
}

static inline uint32_t bvbound_width(bvbound_t *b) {
  return (b->bitsize + 31) >> 5;
}

static inline uint32_t *bvbound_lower(bvbound_t *b) {
  return b->data;
}

static inline uint32_t *bvbound_upper(bvbound_t *b) {
  return b->data + bvbound_width(b);
}



/*
 * Convert bounds to unsigned 64bit number
 * - b->bitsize must be between 1 and 64
 */
extern uint64_t bvbound_lower64(bvbound_t *b);
extern uint64_t bvbound_upper64(bvbound_t *b);





/******************************
 *  SEARCH/ADD/REMOVE BOUNDS  *
 *****************************/

/*
 * Search for a bound on x with the given tag
 * - return NULL if it's not present in the cache
 */
extern bvbound_t *find_bvbound(bvbound_cache_t *cache, bvbound_tag_t tag, int32_t x);


/*
 * Store bounds on x given as 64bit numbers
 * - n = number of bits of x (n must be positive and no more than 64)
 * - there must not be existing bounds on x with the same tag
 * - lower = lower bound
 * - upper = upper bound
 * return the bvbound object added to the table
 */
extern bvbound_t *cache_bvbound64(bvbound_cache_t *cache, bvbound_tag_t tag, int32_t x, uint32_t n, uint64_t lower, uint64_t upper);


/*
 * Same thing but the bounds are given as arrays of 32bit words
 * (cf. bv_constants.h)
 * - n must be positive
 * - there must not be existing bounds on x with the same tag
 * return the bvbound object added to the table
 */
extern bvbound_t *cache_bvbound(bvbound_cache_t *cache, bvbound_tag_t tag, int32_t x, uint32_t n, uint32_t *lower, uint32_t *upper);


/*
 * Delete all records that contain variable x (no change if there's
 * no record with x in the table).
 */
extern void erase_bvbounds(bvbound_cache_t *cache, int32_t x);



#endif /* __BVBOUND_CACHE_H */
