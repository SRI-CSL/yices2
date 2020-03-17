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
 */

#ifndef __MPQ_STORES_H
#define __MPQ_STORES_H

#include <stdint.h>
#include <string.h>
#include <gmp.h>

#include "mt/yices_locks.h"

/* 
 * mpq_link is mpq together with a pointer to the "next" free mpq_link
 * needed to prevent "modifying the contents" of the mpq, as is done
 * in utils/object_stores.[ch]
 */
typedef struct mpq_link_s mpq_link_t;

struct mpq_link_s {
  mpq_t mpq;
  void *next;
};


/*
 * Number of rationals in a block
 */
#define MPQ_BLOCK_COUNT 1024

/*
 * Bank = a block of mpq (links)
 * - blocks are linked in a list
 */
typedef struct mpq_bank_s mpq_bank_t;

struct mpq_bank_s {
  mpq_bank_t *next;
  mpq_link_t block[MPQ_BLOCK_COUNT];
};

/*
 * Store = a list of blocks
 * - allocations are performed via a free list,
 * - or in the first block of the bank list,
 * - or by adding a new block.
 */
typedef struct mpq_store_s {
#ifdef THREAD_SAFE
  yices_lock_t lock;        // a lock protecting the mpq_store
#endif
  mpq_bank_t *bnk;          // first block in the bank list
  mpq_link_t *free_list;    // list of free mpq_links
  uint32_t free_index;      // index of last allocated mpq_link in first block
} mpq_store_t;


/*
 * Initialize store s for object of the given size
 * - n = number of objects in each block
 */
extern void init_mpqstore(mpq_store_t *s);

/*
 * Delete the full store: all banks are freed
 */
extern void delete_mpqstore(mpq_store_t *s);

/*
 * Allocate an mpq
 */
extern mpq_ptr mpqstore_alloc(mpq_store_t *s);

/*
 * Free an allocated mpq_link object: add it to s->free_list.
 * next pointer is stored in mpq_link->next
 */
extern void mpqstore_free(mpq_store_t *s, mpq_ptr mpq);


#endif /* __MPQ_STORES_H */
