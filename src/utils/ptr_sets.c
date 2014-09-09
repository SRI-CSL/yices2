/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>

#include "ptr_sets.h"


/*
 * For debugging: check whether n is a power of two (or zero)
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Hash code for a pointer (cf. hash_functions.c)
 * This is based on Jenkins' lookup3 code
 */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

static uint32_t hash_ptr(const void *p) {
  uint32_t a, b, c;

  a = ((uint32_t) (size_t) p); // lower 32bits
  b = ((uint32_t) ((size_t) p >> 32)); // higher order bits
  c = 0xa783fadd;   // seed

  // this is Jenkins' final mixing
  c ^= b; c -= rot(b,14);
  a ^= c; a -= rot(c,11);
  b ^= a; b -= rot(a,25);
  c ^= b; c -= rot(b,16);
  a ^= c; a -= rot(c,4);
  b ^= a; b -= rot(a,14);
  c ^= b; c -= rot(b,24);

  return c;
}



/*
 * Allocate and initialize a set of size n
 * - n must be a power of two
 */
static ptr_set_t *alloc_ptr_set(uint32_t n) {
  ptr_set_t *tmp;
  uint32_t i;

  assert(n > 0 && is_power_of_two(n));

  if (n > MAX_PTR_SET_SIZE) {
    out_of_memory();
  }

  tmp = (ptr_set_t *) safe_malloc(sizeof(ptr_set_t) + n * sizeof(void *));
  tmp->size = n;
  tmp->nelems = 0;
  tmp->ndeleted = 0;
  for (i=0; i<n; i++) {
    tmp->data[i] = NULL;
  }

  return tmp;
}


/*
 * Check whether p != NULL && p != DELETED_PTR_ELEM
 */
static inline bool live_ptr_elem(const void *p) {
  return (((size_t) p) >> 1) != (size_t) 0;
}


/*
 * Add p to set: sequential array
 * - requires set->nelems < set->size
 * - invariant: the DELETED_PTR_ELEMs occur before any NULL element in set->data
 */
static void add_ptr_to_seq_set(ptr_set_t *set, const void *p) {
  uint32_t i;

  assert(set->nelems < set->size);

  i = 0;
  while (live_ptr_elem(set->data[i])) {
    i ++;
  }

  assert((i < set->nelems + set->ndeleted && set->data[i] == DELETED_PTR_ELEM) ||
	 (i < set->size && set->data[i] == NULL));

  set->data[i] = p;
  set->nelems ++;
  if (set->ndeleted > 0) {
    set->ndeleted --;
  }
}


/*
 * Add p to set when the set is treated as a hash table
 * - requires set->nelems < set->size
 */
static void add_ptr_to_hash_set(ptr_set_t *set, const void *p) {
  uint32_t i, mask;

  assert(set->nelems < set->size);
  assert(is_power_of_two(set->size));

  mask = set->size - 1;
  i = hash_ptr(p) & mask;
  while (live_ptr_elem(set->data[i])) {
    i ++;
    i &= mask;
  }

  assert(set->data[i] == DELETED_PTR_ELEM || set->data[i] == NULL);

  if (set->data[i] == DELETED_PTR_ELEM) {
    assert(set->ndeleted > 0);
    set->ndeleted --;
  }
  set->data[i] = p;
  set->nelems ++;
}



/*
 * Check whether p is present in set: two versions
 */
static bool ptr_in_seq_set(ptr_set_t *set, const void *p) {
  uint32_t i, n;

  n = set->nelems + set->ndeleted;
  assert(n <= set->size);
  for (i=0; i<n; i++) {
    if (set->data[i] == p) {
      return true;
    }
  }

  return false;
}

static bool ptr_in_hash_set(ptr_set_t *set, const void *p) {
  uint32_t i, mask;

  assert(set->nelems + set->ndeleted < set->size);
  assert(is_power_of_two(set->size));

  mask = set->size - 1;
  i = hash_ptr(p) & mask;
  for (;;) {
    if (set->data[i] == p) return true;
    if (set->data[i] == NULL) return false;
    i ++;
    i &= mask;
  }
}



/*
 * Allocate and initialize a set
 * - this creates an empty set of default size
 */
ptr_set_t *new_ptr_set(void) {
  return alloc_ptr_set(DEF_PTR_SET_SIZE);
}




/*
 * Check whether set s contains p
 * - s can be NULL here. NULL is interpreted as the empty set.
 */
bool ptr_set_member(ptr_set_t *s, const void *p) {
  if (s == NULL) {
    return false;
  } else if (s->size <= SMALL_PTR_SET_SIZE) {
    return ptr_in_seq_set(s, p);
  } else {
    return ptr_in_hash_set(s, p);
  }
}


