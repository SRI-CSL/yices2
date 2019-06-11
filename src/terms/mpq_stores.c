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
 * STORE FOR ALLOCATION OF MPQ OBJECTS
 */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
//#include <stdio.h>

#include "utils/memalloc.h"
#include "terms/mpq_aux.h"
#include "terms/mpq_stores.h"
#include "mt/thread_macros.h"

/*
 * Initialize s:
 * - n = number of mpq (link)s per block
 */
static void _o_init_mpqstore(mpq_store_t *s, uint32_t n) {
  assert(0 < n && n <= MAX_OBJ_PER_BLOCK);

  s->bnk = NULL;
  s->free_list = NULL;
  s->free_index = 0;
  s->blocklen = n;
}

void init_mpqstore(mpq_store_t *s, uint32_t n) {
#ifdef THREAD_SAFE
  create_yices_lock(&(s->lock));
#endif
  MT_PROTECT_VOID(s->lock, _o_init_mpqstore(s, n));
}


/*
 * Allocate an mpq in s
 */
static mpq_t *_o_mpqstore_alloc(mpq_store_t *s) {
  uint32_t i;
  mpq_bank_t *new_bank;
  mpq_link_t *obj;

  obj = s->free_list;

  if (obj != NULL) {
    s->free_list = obj->h.next;
    obj->h.next = NULL;  //sanity check: when returned it should still be NULL
    return &obj->mpq;
  }

  i = s->free_index;
  if (i == 0) {
    new_bank = (mpq_bank_t *)safe_malloc(sizeof(mpq_bank_t) + s->blocklen * sizeof(mpq_link_t));
    new_bank->h.next = s->bnk;
    s->bnk = new_bank;
    i = s->blocklen;
  }

  i --;
  s->free_index = i;
  obj = s->bnk->block + i;

  // only initialize when we give it out
  mpq_init2(obj->mpq, 64);
  obj->h.next = NULL; //sanity check: when returned it should still be NULL
  
  return &obj->mpq; //same as obj
}

mpq_t *mpqstore_alloc(mpq_store_t *s) {
  MT_PROTECT(mpq_t *, s->lock, _o_mpqstore_alloc(s));
}


/*
 * Delete all mpqs
 */
static void _o_delete_mpqstore(mpq_store_t *s) {
  mpq_bank_t *b, *next;
  mpq_link_t *obj;
  uint32_t k, i;

  b = s->bnk;
  k = s->free_index;
  while (b != NULL) {
    next = b->h.next;
    for (i=k; i<s->blocklen; i++) {
      obj = b->block + i;
      mpq_clear(obj->mpq);
    }
    safe_free(b);
    k = 0;
    b = next;
  }

  s->bnk = NULL;
  s->free_list = NULL;
  s->free_index = 0;
}

void delete_mpqstore(mpq_store_t *s) {
  MT_PROTECT_VOID(s->lock, _o_delete_mpqstore(s));
#ifdef THREAD_SAFE
  destroy_yices_lock(&(s->lock));
#endif
}


/*
 * Free an allocated mpq: add it to s->free_list.
 * next pointer is stored in mpq->h.next
 */
static void _o_mpqstore_free(mpq_store_t *s, mpq_t *mpq) {
  mpq_link_t *obj;

  obj = (mpq_link_t *)mpq;

  assert(obj->h.next == NULL); //sanity check: it's being returned; it should still be NULL
  
  obj->h.next = s->free_list;
  s->free_list = obj;
}


void mpqstore_free(mpq_store_t *s, mpq_t *mpq) {
  MT_PROTECT_VOID(s->lock, _o_mpqstore_free(s, mpq));
}

