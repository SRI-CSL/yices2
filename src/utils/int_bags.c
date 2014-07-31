/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BAGS OF NON-NEGATIVE INTEGERS
 * - these are implemented as arrays with a hidden header
 * - the code is similar to indexed_vectors but the bags have
 *   support for efficiently removing elements (using a free list)
 */

#include <assert.h>

#include "utils/int_bags.h"

/*
 * Free list elements and indices
 */
enum {
  nil_free_list = -1,
};

// Mask to set/clear the sign bit of an integer
#define SIGN_BIT_MASK ((uint32_t) 0x80000000)

static inline int32_t flip_sign_bit(int32_t k) {
  return (int32_t)(((uint32_t) k) ^ SIGN_BIT_MASK);
}

static inline int32_t free_list_elem(int32_t k) {
  assert(k >= 0);
  return flip_sign_bit(k);
}

static inline int32_t free_list_idx(int32_t k) {
  assert(k < 0);
  return flip_sign_bit(k);
}



/*
 * Add element k to vector *v
 * - k must be >= 0
 * - if *v is NULL, a new bag is allocated
 * - return the index i where k is added
 */
int32_t ibag_add(int32_t **v, int32_t k) {
  int_bag_t *b;
  int32_t *d;
  int32_t i, n;

  assert(k >= 0);

  d = *v;
  if (d == NULL) {
    // first allocation
    n = DEF_INT_BAG_SIZE;
    assert(n <= MAX_INT_BAG_SIZE);
    b = (int_bag_t *) safe_malloc(sizeof(int_bag_t) + n * sizeof(int32_t));
    b->capacity = n;
    b->free = nil_free_list;
    b->nelems = 1;
    b->size = 1;
    b->data[0] = k;
    *v = b->data;
    return 0;

  } else {
    b = ibag_header(d);
    i = b->free;
    if (i != nil_free_list) {
      i = free_list_idx(i);
      b->free = b->data[i];
    } else {
      i = b->size;
      n = b->capacity;
      if (i == n) {
        // make the vector 50% larger
        n ++;
        n += n >> 1;
        if (n > MAX_INT_BAG_SIZE) {
          out_of_memory();
        }
        b = (int_bag_t *) safe_realloc(b, sizeof(int_bag_t) + n * sizeof(int32_t));
        b->capacity =n;
        *v = b->data;
      }
      assert(i <= b->capacity);
      b->size ++;
    }

    b->data[i] = k;
    b->nelems ++;
    return i;
  }
}


/*
 * Empty vector v
 */
void ibag_reset(int32_t *v) {
  int_bag_t *b;

  if (v != NULL) {
    b = ibag_header(v);
    b->size = 0;
    b->nelems = 0;
    b->free = nil_free_list;
  }
}


/*
 * Remove v[i] from vector v
 * - v must be non NULL and i must satisfy 0 <= i < ibag_size(v)
 * - index i is added to the free list
 */
void ibag_clear_elem(int32_t *v, int32_t i) {
  int_bag_t *b;

  assert(v != NULL);
  b = ibag_header(v);
  assert(0 <= i && i < b->size && b->data[i] >= 0);
  b->data[i] = b->free;
  b->free = free_list_elem(i);
  b->nelems --;
}
