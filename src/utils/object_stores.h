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
 * STORES FOR ALLOCATION/RELEASE OF (SMALL) OBJECTS OF FIXED SIZE.
 */

#ifndef __OBJECT_STORES_H
#define __OBJECT_STORES_H

#include <stdint.h>
#include <string.h>

#include "mt/yices_locks.h"

/*
 * Bank = a block of objects
 * - blocks are linked in a list
 * - for correct pointer alignment, we (try to) force the offset
 *   (bank->block - bank) to be a multiple of 8)
 * - we also force object sizes to be multiple of 8 bytes
 *
 * All this is based on the assumption that addresses that are
 * multiple of 8 have the right alignment for all hardware we
 * support.
 */
typedef struct object_bank_s object_bank_t;

struct object_bank_s {
  union {
    object_bank_t *next;
    char padding[8]; // for alignment
  } h;
  char block[0]; // real size determined at allocation time
};

/*
 * Store = a list of blocks
 * - allocations are performed via a free list,
 * - or in the first block of the bank list,
 * - or by adding a new block.
 */
typedef struct object_store_s {
#ifdef THREAD_SAFE
  yices_lock_t lock;   // a lock protecting the object_store
#endif
  object_bank_t *bnk;  // first block in the bank list
  void *free_list;
  uint32_t free_index; // index of last allocated object in first block
  uint32_t objsize;    // size of all objects (in bytes)
  uint32_t blocksize;  // size of blocks (multiple of objsize).
} object_store_t;


/*
 * Bounds on objsize and nobj per block: to avoid numerical overflows,
 * we need objsize * nobj <= UINT32_MAX.  Stores are intended for
 * small objects so the following bounds should be more than enough.
 */
#define MAX_OBJ_SIZE 512
#define MAX_OBJ_PER_BLOCK 4096


/*
 * Initialize store s for object of the given size
 * - n = number of objects in each block
 */
extern void init_objstore(object_store_t *s, uint32_t objsize, uint32_t n);

/*
 * Delete the full store: all banks are freed
 */
extern void delete_objstore(object_store_t *s);

/*
 * Reset the store: remove all objects
 */
extern void reset_objstore(object_store_t *s);


/*
 * Delete with finalizer: apply function f to all
 * objects in the store before freeing the banks.
 */
extern void objstore_delete_finalize(object_store_t *s, void (*f)(void *));

/*
 * Allocate an object
 */
extern void *objstore_alloc(object_store_t *s);

/*
 * Free an allocated object: add it to s->free_list.
 * next pointer is stored in *object
 */
extern void objstore_free(object_store_t *s, void *object);


#endif /* __OBJECT_STORES_H */
