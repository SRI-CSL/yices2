/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STORE FOR ALLOCATION OF (SMALL) OBJECTS
 */

#include <assert.h>
#include <stdbool.h>

#include "utils/memalloc.h"
#include "utils/object_stores.h"

#ifndef NDEBUG

/*
 * For debugging: check alignment
 */
static bool size_is_multiple_of_eight(size_t x) {
  return (x & ((size_t) 7)) == 0;
}

static bool ptr_is_aligned(void *p) {
  return size_is_multiple_of_eight((size_t) p);
}

// p <= q here
static bool offset_is_aligned(void *p, void *q) {
  return size_is_multiple_of_eight(((size_t) q) - ((size_t) p));
}

#endif



/*
 * Initialize s:
 * - objsize = size of all objects in s
 * - n = number of objects per block
 */
void init_objstore(object_store_t *s, uint32_t objsize, uint32_t n) {
  assert(objsize <= MAX_OBJ_SIZE);
  assert(0 < n && n <= MAX_OBJ_PER_BLOCK);

  // round up objsize to a multiple of 8 for pointer alignment
  objsize = (objsize + 7) & ((uint32_t )(~7));

  s->bnk = NULL;
  s->free_list = NULL;
  s->free_index = 0;
  s->objsize = objsize;
  s->blocksize = objsize * n;
}


/*
 * Allocate an object in s
 */
void *objstore_alloc(object_store_t *s) {
  void *tmp;
  uint32_t i;
  object_bank_t *new_bank;

  tmp = s->free_list;
  if (tmp != NULL) {
    // This may be unsafe. Replaced by memcpy.
    //    s->free_list = * ((void **) tmp);
    memcpy(&s->free_list, tmp, sizeof(void*));

    assert(ptr_is_aligned(tmp));

    return tmp;
  }

  i = s->free_index;
  if (i == 0) {
    new_bank = (object_bank_t *) safe_malloc(sizeof(object_bank_t) + s->blocksize * sizeof(char));
    new_bank->h.next = s->bnk;
    s->bnk = new_bank;
    i = s->blocksize;

    assert(offset_is_aligned(new_bank, new_bank->block));
  }

  assert(i >= s->objsize);

  i -= s->objsize;
  s->free_index = i;
  tmp = s->bnk->block + i;

  assert(ptr_is_aligned(tmp));

  return tmp;
}


/*
 * Delete all objects
 */
void delete_objstore(object_store_t *s) {
  object_bank_t *b, *next;

  b = s->bnk;
  while (b != NULL) {
    next = b->h.next;
    safe_free(b);
    b = next;
  }

  s->bnk = NULL;
  s->free_list = NULL;
  s->free_index = 0;
}


/*
 * Apply finalizer f to all objects then delete s
 */
void objstore_delete_finalize(object_store_t *s, void (*f)(void *)) {
  object_bank_t *b, *next;
  void *obj;
  uint32_t k, i;

  b = s->bnk;
  k = s->free_index;
  while (b != NULL) {
    next = b->h.next;
    for (i=k; i<s->blocksize; i += s->objsize) {
      obj = (void *) (b->block + i);
      f(obj);
    }
    safe_free(b);
    k = 0;
    b = next;
  }

  s->bnk = NULL;
  s->free_list = NULL;
  s->free_index = 0;
}


/*
 * Reset store s: remove all objects
 * - keep only one bank
 */
void reset_objstore(object_store_t *s) {
  object_bank_t *b, *next;

  b = s->bnk;
  if (b != NULL) {
    next = b->h.next;
    while (next != NULL) {
      safe_free(b);
      b = next;
      next = b->h.next;
    }
  }

  s->bnk = b;
  s->free_list = NULL;
  s->free_index = 0;
}
