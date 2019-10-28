/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * STORE FOR ALLOCATION OF (SMALL) OBJECTS
 */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>

#include "utils/memalloc.h"
#include "utils/object_stores.h"
#include "mt/thread_macros.h"

#ifndef NDEBUG

/*
 * For debugging: check alignment.
 * We want pointers aligned to multiples of 8.
 */
static bool ptr_is_aligned(void *p) {
  uintptr_t x;

  x = (uintptr_t) p;
  return (x & (uintptr_t) 7) == 0;
}

// p <= q here
static bool offset_is_aligned(void *p, void *q) {
  uintptr_t x, y;

  x = (uintptr_t) p;
  y = (uintptr_t) q;
  assert(x <= y);

  return ((y - x) & (uintptr_t) 7) == 0;
}

#endif



/*
 * Initialize s:
 * - objsize = size of all objects in s
 * - n = number of objects per block
 */
static void _o_init_objstore(object_store_t *s, uint32_t objsize, uint32_t n) {
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

void init_objstore(object_store_t *s, uint32_t objsize, uint32_t n) {
#ifdef THREAD_SAFE
  create_yices_lock(&(s->lock));
#endif
  MT_PROTECT_VOID(s->lock, _o_init_objstore(s, objsize, n));
}


/*
 * Allocate an object in s
 */
static void *_o_objstore_alloc(object_store_t *s) {
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

void *objstore_alloc(object_store_t *s) {
  MT_PROTECT(void *, s->lock, _o_objstore_alloc(s));
}


/*
 * Delete all objects
 */
static void _o_delete_objstore(object_store_t *s) {
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

void delete_objstore(object_store_t *s) {
  MT_PROTECT_VOID(s->lock, _o_delete_objstore(s));
#ifdef THREAD_SAFE
  destroy_yices_lock(&(s->lock));
#endif
}

/*
 * Free an allocated object: add it to s->free_list.
 * next pointer is stored in *object
 */
static void _o_objstore_free(object_store_t *s, void *object) {
  /*
   * BUG: This violates the strict aliasing rules and causes
   * errors when optimizations are enabled?
   */
  //  * ((void **) object) = s->free_list;
  // Try this instead.
  memcpy(object, &s->free_list, sizeof(void*));
  s->free_list = object;
}
void objstore_free(object_store_t *s, void *object) {
  MT_PROTECT_VOID(s->lock, _o_objstore_free(s, object));
}

/*
 * Apply finalizer f to all objects then delete s
 */
static void _o_objstore_delete_finalize(object_store_t *s, void (*f)(void *)) {
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
void objstore_delete_finalize(object_store_t *s, void (*f)(void *)) {
  MT_PROTECT_VOID(s->lock, _o_objstore_delete_finalize(s, f));
#ifdef THREAD_SAFE
  destroy_yices_lock(&(s->lock));
#endif
}


/*
 * Reset store s: remove all objects
 * - keep only one bank
 */
static void _o_reset_objstore(object_store_t *s) {
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
void reset_objstore(object_store_t *s) {
  MT_PROTECT_VOID(s->lock, _o_reset_objstore(s));
}
