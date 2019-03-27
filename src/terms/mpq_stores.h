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
 * STORES FOR ALLOCATION/RELEASE OF MPQ'S
 * Could be made parametric in the MPQ.
 * Could be improved so that we initialize the mpq on demand
 */

#ifndef __MPQ_STORES_H
#define __MPQ_STORES_H

#include <stdint.h>
#include <string.h>
#include <gmp.h>

#include "mt/yices_locks.h"

/* 
 * mpq_link is mpq together with a pointer to the "next" free mpq_link
 * needed to prevent "modifying the contents" of the mpq
 */
typedef struct mpq_link_s mpq_link_t;

struct mpq_link_s {
  mpq_t mpq;
  void* next;
};


/*
 * Bank = a block of mpqs
 * - blocks are linked in a list
 * - for correct pointer alignment, we (try to) force the offset
 *   (bank->block - bank) to be a multiple of 8)
 * - we also force object sizes to be multiple of 8 bytes
 *
 * All this is based on the assumption that addresses that are
 * multiple of 8 have the right alignment for all hardware we
 * support.
 */
typedef struct mpq_bank_s mpq_bank_t;

struct mpq_bank_s {
  union {
    mpq_bank_t *next;
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
typedef struct mpq_store_s {
#ifdef THREAD_SAFE
  yices_lock_t lock;   // a lock protecting the mpq_store
#endif
  mpq_bank_t *bnk;        // first block in the bank list
  mpq_link_t *free_list;  // list of free mpq_links
  uint32_t free_index;    // index of last allocated mpq_link in first block
  uint32_t linksize;      // size of mpq (in bytes)
  uint32_t blocksize;     // size of blocks (multiple of mpqsize).
  uint32_t blockcount;    // number of blocks (for fine tuning).
  
} mpq_store_t;


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
extern void init_mpqstore(mpq_store_t *s, uint32_t n);

/*
 * Delete the full store: all banks are freed
 */
extern void delete_mpqstore(mpq_store_t *s);

/*
 * Allocate an mpq
 */
extern mpq_t *mpqstore_alloc(mpq_store_t *s);

/*
 * Free an allocated mpq_link object: add it to s->free_list.
 * next pointer is stored in mpq_link->next
 */
extern void mpqstore_free(mpq_store_t *s, mpq_t *mpq);


#endif /* __MPQ_STORES_H */
