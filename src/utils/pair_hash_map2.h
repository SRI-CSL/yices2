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
 * HASH MAP2
 *
 * - map pairs of 32bit integers to 32bit integers
 * - supports push and pop.
 */

/*
 * When we apply the lift-if rules during internalization,
 * we must map pairs of terms to literals.
 *
 * Example: lifting if-then-else in equalities rewrites
 *  (eq t1 (ite c t2 t3)) to (ite c (eq t1 t2) (eq t1 t3)).
 * When the right hand side is processed, then (eq t1 t2) and
 * (eq t1 t3) are mapped to two literals l1 and l2. We keep
 * the mappings <t1, t2> --> l1 and <t1, t3> --> l2 in
 * a hash table.
 */

#ifndef __PAIR_HASH_MAP2_H
#define __PAIR_HASH_MAP2_H

#include <stdint.h>

/*
 * Each element in the table is a triple of integers <k0, k1, v>
 * - key = pair <k0, k1>
 * - value = integer val
 */
typedef struct pmap2_rec_s {
  int32_t k0;
  int32_t k1;
  int32_t val;
} pmap2_rec_t;


/*
 * Structure for allocation of records
 * - block is an array of pointers of size 'capacity'
 * - nblocks = number of blocks allocated:
 * - free_block = index of the first empty block
 *   we always have 0 <= free_block <= nblocks <= capacity
 *
 * - for 0 <= i < nblocks:
 *   block[i] = pointer to an array of PMAP2_BLOCK_SIZE records
 * - for nblocks <= i < capacity:
 *   block[i] = uninitialized pointer
 *
 * - for 0 <= i < free_block: block[i] contains data
 *   for free_block <= i < blocks: block[i] is empty
 *
 * When free_block = 0, the whole bank is empty. Otherwise,
 * new records are allocated in block[free_block-1]:
 * - alloc_ptr = index of the first available record in block[free_block-1]
 * - for 0 <= i < free_block-1, block[i] is full.
 */
typedef struct pmap2_bank_s {
  uint32_t capacity;
  uint32_t nblocks;
  uint32_t free_block;
  uint32_t alloc_ptr;
  pmap2_rec_t **block;
} pmap2_bank_t;

// size of each block
#define PMAP2_BLOCK_SIZE 500

// initial and maximal size of the block array
#define PMAP2_DEF_BANK_SIZE 10
#define PMAP2_MAX_BANK_SIZE (UINT32_MAX/sizeof(pmap2_rec_t *))


/*
 * Stack of allocation marks for push and pop;
 * - each element in the stack has a level k>0 and
 *   an allocation mark = a pair <block id, index in that block>
 * - if the mark for level k is <i, p> then the first record
 *   allocated at level k was block[i][p].
 * - nmarks = number of elements stored in the stack:
 *   the stack elements are in data[0 ... nmarks - 1]
 * - size = size of array data
 * - current_level = current allocation level
 * - top_level = maximal allocation level in the stack:
 *   top_level = 0 if the stack is empty or
 *   top_level = data[nmarks-1].level otherwise
 */
typedef struct pmap2_mark_s {
  uint32_t level;
  uint32_t block_id;
  uint32_t alloc_idx;
} pmap2_mark_t;

typedef struct pmap2_stack_s {
  uint32_t current_level;
  uint32_t top_level;
  uint32_t nmarks;
  uint32_t size;
  pmap2_mark_t *data;
} pmap2_stack_t;


#define PMAP2_DEF_STACK_SIZE 10
#define PMAP2_MAX_STACK_SIZE (UINT32_MAX/sizeof(pmap2_mark_t))


/*
 * Hash table:
 * - stores pointers to triples <k0, k1, value>
 *   data[h] = NULL means slot h is empty
 *   data[h] = DELETED_REC means slot h is deleted
 * - same implementation as int_hash_table etc.
 */
typedef struct pmap2_htbl_s {
  pmap2_rec_t **data;
  uint32_t size;
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} pmap2_htbl_t;


/*
 * Marker for deleted elements
 */
#define PMAP2_DELETED ((pmap2_rec_t *) 1)


/*
 * Default and maximal size
 */
#define PMAP2_DEF_HTBL_SIZE 128
#define PMAP2_MAX_HTBL_SIZE (UINT32_MAX/sizeof(pmap2_rec_t *))


/*
 * Ratios for resizing and removing deleted elements
 */
#define PMAP2_HTBL_RESIZE_RATIO 0.6
#define PMAP2_HTBL_CLEANUP_RATIO 0.2


/*
 * Full hash map table
 */
typedef struct pmap2_s {
  pmap2_htbl_t htbl;
  pmap2_stack_t stack;
  pmap2_bank_t bank;
} pmap2_t;




/***********************
 *  CREATION/DELETION  *
 **********************/

/*
 * Initialize the map: memory for stack and bank is not
 * allocated yet.
 */
extern void init_pmap2(pmap2_t *map);


/*
 * Delete all objects stored and all allocated memory
 */
extern void delete_pmap2(pmap2_t *pmap);


/*
 * Empty the table and set current_level to 0
 */
extern void reset_pmap2(pmap2_t *pmap);


/*
 * Push
 */
static inline void pmap2_push(pmap2_t *pmap) {
  pmap->stack.current_level ++;
}


/*
 * Pop: delete all objects created at the current level
 * then decrement current_level. Should not be called at level 0.
 */
extern void pmap2_pop(pmap2_t *pmap);


/*
 * Set level: same effect as calling push n times from the initial state.
 * - this is used to ensure consistency between pmap2->current_level
 *   and context->base_level if the pmap2 is created when the context
 *   has non-zero base_level
 */
static inline void pmap2_set_level(pmap2_t *pmap, uint32_t n) {
  pmap->stack.current_level = n;
}



/********************
 *  MAP OPERATIONS  *
 *******************/

/*
 * Find the record with with key <k0, k1>
 * - return NULL if there's no such record in the table.
 */
extern pmap2_rec_t *pmap2_find(const pmap2_t *pmap, int32_t k0, int32_t k1);


/*
 * Find or add the record with key <k0, k1>
 * - return the existing record if it exists in the table
 * - otherwise: create a new record with key = <k0, k1> and val = -1,
 *   add it to the table and return a pointer to the new record.
 * The caller must check val to determine whether the record is new
 * or not and set val to something else than -1.
 */
extern pmap2_rec_t *pmap2_get(pmap2_t *pmap, int32_t k0l, int32_t k1);




/***************
 *  ITERATOR   *
 **************/

/*
 * Call f(aux, p) on every record p stored in pmap
 * - f must not have any side effect on pmap
 */
typedef void (*pmap2_iterator_t)(void *aux, const pmap2_rec_t *p);

extern void pmap2_iterate(pmap2_t *pmap, void *aux, pmap2_iterator_t f);



#endif /* __PAIR_HASH_MAP2_H */
