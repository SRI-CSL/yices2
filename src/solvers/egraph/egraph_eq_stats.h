/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * HASH TABLE TO COLLECT DATA ON INTERACTIONS BETWEEN THE EGRAPH AND A
 * SATELLITE SOLVER
 */

/*
 * Each element in the table stores statistics
 * about a pair of theory veriables x[0] and x[1]
 * - currently we keep:
 * - the number of times, the egraph propagates (x[0] == x[1])
 * - the number of times, the egraph propagates (x[0] != x[1])
 * - the number of times, the equality (x[0] == x[1]) is used in
 *   a conflict explanation
 */

#ifndef __EGRAPH_EQ_STATS_H
#define __EGRAPH_EQ_STATS_H

#include <assert.h>
#include <stdint.h>
#include <stdio.h>


/*
 * Each record in the table stores
 * - a pair <x[0], x[1]>
 * - the hash code for that triple
 * - five counters ctr[0], ctr[1], .. ctr[4]
 */
typedef struct egeq_elem_s {
  uint32_t hash;
  int32_t x[2];
  uint32_t ctr[5];
} egeq_elem_t;


/*
 * Structure for allocation of records:
 * - block is an array of size 'capacity'
 * - for 0 <= i < nblocks:
 *   block[i] is a pointer to an allocated block (an array of
 *     EGEQ_BLOCK_SIZE records)
 * - for nblocks <= i < capacity: block[i] is not initialized
 * - for 0 <= i < free_block: block[i] contains data
 * - for free_block <= i < nblocks, block[i] is empty
 *
 * If the bank is empty, then free_blocks = 0
 *
 * Otherwise, free_block > 0 and records are allocated in block[free_block-1]
 * - alloc_ptr = index of the first available slot in block[free_block-1]
 * - for 0 <= i < free_block - 1, block[i] is full
 */
typedef struct egeq_bank_s {
  uint32_t capacity;
  uint32_t nblocks;
  uint32_t free_block;
  uint32_t alloc_ptr;
  egeq_elem_t **block;
} egeq_bank_t;

#define EGEQ_BLOCK_SIZE 120

#define DEF_EGEQ_BANK_SIZE 4
#define MAX_EGEQ_BANK_SIZE (UINT32_MAX/sizeof(egeq_elem_t*))


/*
 * Stack of allocation marks for push/pop operations
 * - each element in the stack has a level k>0
 *   and keeps a pointer to the first record allocated at that level
 *   the pointer consists of a pair <block id, index in block>
 * - the stack elements are in data[0 ... nmarks-1]
 * - current_level = current allocation level (incremented by push)
 * - top_level = 0 if the stack is empty
 *   otherwise top_level = maximal level in stack = data[nmarks-1].level
 */
typedef struct egeq_mark_s {
  uint32_t level;
  uint32_t blk_id;
  uint32_t index;
} egeq_mark_t;

typedef struct egeq_levstack_s {
  uint32_t current_level;
  uint32_t top_level;
  uint32_t nmarks;
  uint32_t size;
  egeq_mark_t *data;
} egeq_levstack_t;

#define DEF_EGEQ_STACK_SIZE 10
#define MAX_EGEQ_STACK_SIZE (UINT32_MAX/sizeof(egeq_mark_t))


/*
 * Hash table (see int_hash_table, etc.)
 */
typedef struct egeq_htbl_s {
  egeq_elem_t **data;  // hash table proper
  uint32_t size;        // its size (power of 2)
  uint32_t nelems;      // number of elements
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} egeq_htbl_t;


/*
 * Marker for deleted elements
 */
#define DELETED_EG_ELEM ((egeq_elem_t *) 1)

/*
 * DEF_EGEQ_HTBL_SIZE must be a power of 2, smaller than MAX_EGEQ_HTBL_SIZE
 */
#define DEF_EGEQ_HTBL_SIZE 32
#define MAX_EGEQ_HTBL_SIZE (UINT32_MAX/sizeof(egeq_elem_t*))
#define EGEQ_HTBL_RESIZE_RATIO  0.6
#define EGEQ_HTBL_CLEANUP_RATIO 0.2


/*
 * Full table
 */
typedef struct egeq_s {
  egeq_htbl_t htbl;
  egeq_levstack_t stack;
  egeq_bank_t bank;
} egeq_t;




/***********************
 *  CREATION/DELETION  *
 **********************/

/*
 * Initialize the table: memory for stack and bank is not
 * allocated yet.
 */
extern void init_egeq(egeq_t *egeq);


/*
 * Delete all objects stored in the table and all allocated memory
 */
extern void delete_egeq(egeq_t *egeq);


/*
 * Empty the table and set current_level to 0
 */
extern void reset_egeq(egeq_t *egeq);


/*
 * Push
 */
static inline void egeq_push(egeq_t *egeq) {
  egeq->stack.current_level ++;
}


/*
 * Pop: delete all objects created at the current level
 * then decrement current_level. Should not be called at level 0.
 */
extern void egeq_pop(egeq_t *egeq);


/*
 * Set level: same effect as calling push n times from the initial state.
 * - this is used to ensure consistency between egeq->current_level
 *   and solver->base_level (solver may be the simplex solver) if the table
 *   is created when the solver has non-zero base_level
 */
static inline void egeq_set_level(egeq_t *egeq, uint32_t n) {
  egeq->stack.current_level = n;
}


/****************
 *  OPERATIONS  *
 ***************/

/*
 * Find a record for <x, y>
 * - return NULL if there's no matching record in the hash table
 */
extern egeq_elem_t *egeq_find(egeq_t *egeq, int32_t x, int32_t y);

/*
 * Find or store element <x, y>
 * - a pointer to the existing or new element is returned
 * - for a new element, all counters are initialized to zero
 */
extern egeq_elem_t *egeq_get(egeq_t *egeq, int32_t x, int32_t y);


/*
 * Increment counter k of the pair <x, y>
 */
static inline void egeq_incr(egeq_t *egeq, int32_t x, int32_t y, uint32_t k) {
  egeq_elem_t *e;

  assert(0 <= k && k < 5);
  e = egeq_get(egeq, x, y);
  e->ctr[k] ++;
}


/*
 * Print the table
 */
extern void print_egeq(FILE *f, egeq_t *egeq);


#endif /* __EGRAP_EQ_STATS_H */
