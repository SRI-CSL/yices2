/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>

#include "utils/ptr_sets.h"


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

static uint32_t hash_ptr(void *p) {
  uint64_t tmp;
  uint32_t a, b, c;

  /*
   * we first convert p to uint64_t
   * because something like ((size_t) p) >> 32
   * is an undefined operation if size_t is 32bits.
   */
  tmp = (uint64_t) ((uintptr_t) p);
  a = (uint32_t) tmp;         // lower 32bits
  b = (uint32_t) (tmp >> 32); // higher order bits
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
 * Add p to set: sequential array
 * - requires set->nelems < set->size
 * - invariant: the DELETED_PTR_ELEMs occur before any NULL element in set->data
 */
static void add_ptr_to_seq_set(ptr_set_t *set, void *p) {
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
static void add_ptr_to_hash_set(ptr_set_t *set, void *p) {
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
 * Generic form
 */
static void add_ptr_to_set(ptr_set_t *set, void *p) {
  if (set->size <= SMALL_PTR_SET_SIZE) {
    add_ptr_to_seq_set(set, p);
  } else {
    add_ptr_to_hash_set(set, p);
  }
}


/*
 * Add p to a freshly initialized set
 */
static void clean_add_ptr_to_seq_set(ptr_set_t *set, void *p) {
  uint32_t i;

  assert(set->ndeleted == 0 && set->nelems < set->size);
  i = set->nelems;
  set->data[i] = p;
  set->nelems = i + 1;
}

static void clean_add_ptr_to_hash_set(ptr_set_t *set, void *p) {
  uint32_t i, mask;

  assert(set->ndeleted == 0 && set->nelems < set->size);
  assert(is_power_of_two(set->size));

  mask = set->size - 1;
  i = hash_ptr(p) & mask;
  while (set->data[i] != NULL) {
    i ++;
    i &= mask;
  }

  set->data[i] = p;
  set->nelems ++;
}

static void clean_add_ptr_to_set(ptr_set_t *set, void *p) {
  if (set->size <= SMALL_PTR_SET_SIZE) {
    clean_add_ptr_to_seq_set(set, p);
  } else {
    clean_add_ptr_to_hash_set(set, p);
  }
}


/*
 * Copy set s1 into fresh set s2
 * - s2 must be large enough (i.e., s2->size >= s1->nelems)
 */
static void copy_ptr_set(ptr_set_t *s2, ptr_set_t *s1) {
  void *p;
  uint32_t i, n;

  n = s1->size;
  if (s2->size > SMALL_PTR_SET_SIZE) {
    // s2 is used as a hash table
    for (i=0; i<n; i++) {
      p = s1->data[i];
      if (live_ptr_elem(p)) {
	clean_add_ptr_to_hash_set(s2, p);
      }
    }
  } else {
    // s2 is a sequential array
    for (i=0; i<n; i++) {
      p = s1->data[i];
      if (live_ptr_elem(p)) {
	clean_add_ptr_to_seq_set(s2, p);
      }
    }
  }
}


/*
 * Resize set:
 * - if set is NULL, return a new set of default size
 * - otherwise, create a new set of twice set's size
 *   then copy the content into it and free set.
 */
static ptr_set_t *resize_ptr_set(ptr_set_t *set) {
  ptr_set_t *tmp;

  if (set == NULL) {
    tmp = alloc_ptr_set(DEF_PTR_SET_SIZE);
  } else {
    tmp = alloc_ptr_set(set->size << 1);  // double the size
    copy_ptr_set(tmp, set);
    free_ptr_set(set);
  }

  return tmp;
}


/*
 * Shrink set:
 * - create a new set of half size then
 *   copy the set's content into it
 */
static ptr_set_t *shrink_ptr_set(ptr_set_t *set) {
  ptr_set_t *tmp;

  assert(set->size > DEF_PTR_SET_SIZE && set->nelems <= set->size/2);

  tmp = alloc_ptr_set(set->size >> 1); // half the size
  copy_ptr_set(tmp, set);
  free_ptr_set(set);

  return tmp;
}





/*
 * Check whether p is present in set: two versions
 */
static bool ptr_in_seq_set(ptr_set_t *set, void *p) {
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

static bool ptr_in_hash_set(ptr_set_t *set, void *p) {
  uint32_t i, j, mask;

  assert(set->size > 0 && is_power_of_two(set->size));

  mask = set->size - 1;
  j = hash_ptr(p) & mask;
  i = j;
  do {
    if (set->data[i] == p) return true;
    if (set->data[i] == NULL) break;
    i ++;
    i &= mask;
  } while (i != j);

  return false;
}


/*
 * Remove p from set
 * - p must be present in set
 * - if p occurs serval times, only one occurrence is removed
 */
static void remove_ptr_from_seq_set(ptr_set_t *set, void *p) {
  uint32_t i;

  assert(ptr_in_seq_set(set, p));

  i = 0;
  while (set->data[i] != p) {
    i ++;
  }
  set->data[i] = DELETED_PTR_ELEM;
  set->nelems --;
  set->ndeleted ++;
}

static void remove_ptr_from_hash_set(ptr_set_t *set, void *p) {
  uint32_t i, mask;

  assert(ptr_in_hash_set(set, p));

  mask = set->size - 1;
  i = hash_ptr(p) & mask;
  while (set->data[i] != p) {
    i ++;
    i &= mask;
  }
  set->data[i] = DELETED_PTR_ELEM;
  set->nelems --;
  set->ndeleted ++;
}

static void remove_ptr_from_set(ptr_set_t *set, void *p) {
  if (set->size <= SMALL_PTR_SET_SIZE) {
    remove_ptr_from_seq_set(set, p);
  } else {
    remove_ptr_from_hash_set(set, p);
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
bool ptr_set_member(ptr_set_t *s, void *p) {
  if (s == NULL) {
    return false;
  } else if (s->size <= SMALL_PTR_SET_SIZE) {
    return ptr_in_seq_set(s, p);
  } else {
    return ptr_in_hash_set(s, p);
  }
}


/*
 * Check whether set is full: i.e., require resizing before
 * we add something to it.
 */
static bool ptr_set_is_full(ptr_set_t *set) {
  if (set == NULL) {
    return true;
  }

  if (set->size <= SMALL_PTR_SET_SIZE) {
    assert(set->nelems + set->ndeleted <= set->size);
    return set->nelems == set->size;
  } else {
    return set->nelems > set->size * PTR_SET_RESIZE_RATIO;
  }
}


/*
 * Add p to the set *s.
 * - p must be distinct from NULL and from DELETED_PTR_ELEM
 * - if *s is NULL, this function creates a new set of
 *   default size that contains the singleton { p } and stores
 *   this new set in *s.
 * - if *s is non NULL, then p is added to the set pointed
 *   to by *s. This may cause of new set descriptor to
 *   be allocated and stored in *s (and the original set
 *   is freed).
 *
 * The function does not check whether p is already present.
 * It will add an element to *s no-matter what (so *s may
 * contain duplicates).
 */
void ptr_set_add(ptr_set_t **s, void *p) {
  ptr_set_t *set;

  assert(live_ptr_elem(p));

  set = *s;
  if (ptr_set_is_full(set)) {
    set = resize_ptr_set(set);
    *s = set;
    clean_add_ptr_to_set(set, p);
  } else {
    add_ptr_to_set(set, p);
  }
}


/*
 * Check whether set needs to be shrunk
 */
static bool ptr_set_is_near_empty(ptr_set_t *set) {
  assert(set != NULL);

  if (set->size <= DEF_PTR_SET_SIZE) {
    return false;
  } else {
    // same rule for the sequential and hash table representations.
    return set->nelems < set->size * PTR_SET_SHRINK_RATIO;
  }
}

/*
 * Remove p from set *s
 * - p must be distinct from NULL and from DELETED_PTR_ELEM
 * - p must be present in *s (so *s must be non-NULL)
 * - *s may be updated to a new set descriptor if the removal
 *   of p causes a reduction in size.
 *
 * If s contains p multiple times, then only one occurrence
 * of p is removed.
 */
void ptr_set_remove(ptr_set_t **s, void *p) {
  ptr_set_t *set;

  assert(live_ptr_elem(p));
  assert(ptr_set_member(*s, p));

  set = *s;
  remove_ptr_from_set(set, p);
  if (ptr_set_is_near_empty(set)) {
    set = shrink_ptr_set(set);
    *s = set;
  }
}



/*
 * Add p to *s if it's not present.
 * - updates *s as explained in ptr_set_add
 * - returns true if p is added (i.e., p was not in *s when the function was called)
 * - returns false otherwise and leaves *s unchanged.
 */
bool ptr_set_add_if_absent(ptr_set_t **s, void *p) {
  // TBD: We could avoid scanning the set twice.
  if (ptr_set_member(*s, p)) {
    return false;
  }
  ptr_set_add(s, p);
  return true;
}


/*
 * Remove p from *s if it's present
 * - if p is not present in *s, then *s is unchanged and the function
 *   returns false.
 * - otherwise, one occurrence of p is removed from *s, then *s
 *   may be updated as in ptr_set_remove, and the function returns true.
 */
bool ptr_set_remove_if_present(ptr_set_t **s, void *p) {
  if (ptr_set_member(*s, p)) {
    ptr_set_remove(s, p);
    return true;
  }
  return false;
}


/*
 * Apply function f to all the elements of s
 */
void ptr_set_iterate(ptr_set_t *s, void *aux, ptr_set_iterator_t f) {
  void *p;
  uint32_t i, n;

  if (s != NULL) {
    n = s->size;
    for (i=0; i<n; i++) {
      p = s->data[i];
      if (live_ptr_elem(p)) {
	f(aux, p);
      }
    }
  }
}
