/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SETS OF UNSIGNED INTEGERS REPRESENTED AS BITVECTORS
 */

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>

#include "utils/int_bv_sets.h"


/*
 * Initialize set:
 * - n = initial size. If n == 0, the default size is used.
 * - the set is initially empty
 */
void init_int_bvset(int_bvset_t *set, uint32_t n) {
  if (n == 0) {
    n = DEF_INT_BVSET_SIZE;
  } else {
    // round up to a multiple of 8
    n = (n + 7) & ~((uint32_t) 7);
  }

  set->size = n;
  set->nbits = 0;
  set->data = allocate_bitvector(n);
}


/*
 * Delete
 */
void delete_int_bvset(int_bvset_t *set) {
  delete_bitvector(set->data);
  set->data = NULL;
}


/*
 * Increase the size: make set large enough for adding element x
 */
static void resize_int_bvset(int_bvset_t *set, uint32_t x) {
  uint32_t n;

  assert(x >= set->nbits);

  //  printf("--> resize_bvset: x = %"PRIu32", nbits = %"PRIu32"\n", x, set->nbits);
  // we need at least x+1 elements, rounded up to the next multiple of 8
  x = (x + 8) & ~((uint32_t) 7);

  n = set->size;
  if (x > n) {
    // new size = max(2*n, x)
    n += n;
    if (x > n) n = x;
    set->size = n;
    //    set->data = extend_bitvector(set->data, n);
    set->data = safe_realloc(set->data, n>>3);
  }

  // clear all bits from set->nbits to x
  n = set->nbits;
  set->nbits = x;
  n >>= 3;
  x >>= 3;
  assert(n < x && x <= (set->size>>3));

  /*
   * This memset is critical for GCC 4.1.1 on x86_64
   * GCC -O3 compiles this to a call to memset
   * GCC -Os inlines this to "rep stos", which is much faster
   */
  memset(set->data + n, 0, x - n);
}


/*
 * Add x to the set and check whether x was present
 */
bool int_bvset_add_check(int_bvset_t *set, uint32_t x) {
  uint32_t j;
  byte_t mask, u;

  if (x >= set->nbits) {
    resize_int_bvset(set, x);
  }

  j = x >> 3;
  mask = 1 << (x & 0x7);
  u = set->data[j];
  if (u & mask) {
    return false;
  } else {
    set->data[j] |= mask;
    return true;
  }
}


/*
 * Add x to the set
 */
void int_bvset_add(int_bvset_t *set, uint32_t x) {
  uint32_t j;
  byte_t mask;

  if (x >= set->nbits) {
    resize_int_bvset(set, x);
  }

  j = x >> 3;
  mask = 1 << (x & 0x7);
  set->data[j] |= mask;

  assert(int_bvset_member(set, x));
}


/*
 * Remove x from the set
 */
void int_bvset_remove(int_bvset_t *set, uint32_t x) {
  uint32_t j;
  byte_t mask;

  if (x < set->nbits) {
    j = x >> 3;
    mask = 1 << (x & 0x7);
    set->data[j] &= ~mask;
  }

  assert(!int_bvset_member(set, x));
}
