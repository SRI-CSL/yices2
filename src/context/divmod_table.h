/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Table for internalization of div/mod/floor/ceil
 *
 * When we internalize a term like (div x k), we map
 * it to an integer variable i in the arithmetic solver,
 * and we add axioms like i <= x/k < i+1.
 * 
 * We also implicitly need (div x k) to internalize (mod x k) and
 * (divides k x). To avoid generating the definition of (div x k)
 * several times, we store the mapping (div x k) --> i in a hash table
 * defined here.
 *
 * The table has support for push/pop/reset.
 *
 * By definition, we have
 *  (div x k) = floor(x/k) if k>0
 *  (div x k) = ceil(x/k)  if k<0
 * so every element in the table consists of 
 * a key = triple <tag, variable, rational constant>
 * and a value = integer variables.
 *
 * The tag is either CEIL or FLOOR.
 */

#ifndef __DIVMOD_TABLE_H
#define __DIVMOD_TABLE_H

#include <stdint.h>

#include "terms/rationals.h"


/*
 * Element in the table:
 * - key: tag, var, rational
 * - val: var
 */
typedef enum {
  DIVMOD_FLOOR_TAG,
  DIVMOD_CEIL_TAG,
} divmod_tag_t;

typedef struct divmod_rec_s {
  divmod_tag_t tag;
  int32_t var;
  rational_t q;
  int32_t val;    // value
} divmod_rec_t;


/*
 * Data structure for allocation of records: same as pair_hash_map2.h.
 * - block = an array of pointers to blocks
 * - capacity = size of array block
 * - nblocks = number of blocks actually allocated
 * - free_block = index of the first empty block
 * We have 0 <= free_block <= nblocks <= capacity.
 * 
 * For 0 <= i < nblocks: block[i] points to a block.
 * For nblocks <= i < capacity: block[i] is not intialized.
 *
 * For 0 <= i < free_block-1: block[i] is full.
 * For i = free_block-1: current block where records are allocated.
 * For free_block <= i < nblocks: block[i] is empty.
 *
 * If free_block is 0, the whole bank is empty. Otherwise,
 * records are allocated in block[free_block - 1].
 * - alloc_ptr = index of the first available record in block[free_block - 1].
 * - if alloc_ptr = BLOCK_SIZE then block[free_block - 1 is full.
 */
typedef struct divmod_bank_s {
  uint32_t capacity;
  uint32_t nblocks;
  uint32_t free_block;
  uint32_t alloc_ptr;
  divmod_rec_t **block;
} divmod_bank_t;

// size of each block
#define DIVMOD_BLOCK_SIZE 100

// initial and maximal size of the block array
#define DIVMOD_DEF_BANK_SIZE 10
#define DIVMOD_MAX_BANK_SIZE (UINT32_MAX/sizeof(divmod_rec_t *))


/*
 * Stack of allocation marks for push/pop
 * - each element in the stack has a level k>0 
 *   and an allocation mark = a pair <block index, alloc index>
 *   the alloc_index is an index in block[block_index].
 * - if the mark for level k is <i, p> then the first
 *   record allocated at level k was block[i][p].
 * - nmarks = number of elements in the stack
 * - data = array to store stack elements
 * - size = size of the data array
 * - current_level = counter to keep track of levels
 * - top_level = maximal level in the stack.
 *   if the stack is empty, top_level is 0
 *   otherwise, it's equal to data[nmarks - 1].level
 */
typedef struct divmod_mark_s {
  uint32_t level;
  uint32_t block_id;
  uint32_t alloc_idx;
} divmod_mark_t;

typedef struct divmod_stack_s {
  uint32_t current_level;
  uint32_t top_level;
  uint32_t nmarks;
  uint32_t size;
  divmod_mark_t *data;
} divmod_stack_t;

#define DIVMOD_DEF_STACK_SIZE 10
#define DIVMOD_MAX_STACK_SIZE (UINT32_MAX/sizeof(divmod_mark_t))

/*
 * Hash table:
 * - stores pointers to records
 *   data[h] = NULL means slot h is empty
 *   data[h] = DELETED means slot h is free
 * - otherwise data[h] points to a record
 *   r = <tag, var, constant, val>
 * - the hash value is computed from <tag, var, constant>
 */
typedef struct divmod_htbl_s {
  divmod_rec_t **data;
  uint32_t size;
  uint32_t nelems;
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} divmod_htbl_t;


// marked for deleted elements
#define DIVMOD_DELETED ((divmod_rec_t *) 1)

// default and max size
#define DIVMOD_DEF_HTBL_SIZE 64
#define DIVMOD_MAX_HTBL_SIZE (UINT32_MAX/sizeof(divmod_rec_t *))


/*
 * Ratios for resizing and cleanup
 */
#define DIVMOD_HTBL_RESIZE_RATIO 0.6
#define DIVMOD_HTBL_CLEANUP_RATIO 0.2


/*
 * Full table:
 * - auxiliary rationals one is initialized to 1 
 */
typedef struct divmod_tbl_s {
  divmod_htbl_t htbl;
  divmod_stack_t stack;
  divmod_bank_t bank;
  rational_t one;
} divmod_tbl_t;


/******************************
 *  CREATION/DELETION/RESET   *
 *****************************/

/*
 * Initialize the table.
 */
extern void init_divmod_table(divmod_tbl_t *tbl);

/*
 * Delete it: free memory
 */
extern void delete_divmod_table(divmod_tbl_t *tbl);

/*
 * Reset: empty the table and reset the stack
 */
extern void reset_divmod_table(divmod_tbl_t *tbl);


/*
 * Push
 */
static inline void divmod_table_push(divmod_tbl_t *tbl) {
  tbl->stack.current_level ++;
}

/*
 * Pop: delete all records stored at the current level
 * then decrement current_level. The current level must be positive.
 */
extern void divmod_table_pop(divmod_tbl_t *tbl);

/*
 * Set level: same effect as calling push n times from the initial state.
 * - this is used to ensure consistency between the current_level
 *   and context->base_level if the table is created when the context
 *   has non-zero base_level
 */
static inline void divmod_table_set_level(divmod_tbl_t *tbl, uint32_t n) {
  tbl->stack.current_level = n;
}


/********************
 *  MAP OPERATIONS  *
 *******************/

/*
 * Find the record with with key <tag, v, q>
 * - return NULL if there's no such record in the table.
 */
extern divmod_rec_t *divmod_table_find(divmod_tbl_t *tbl, divmod_tag_t tag, int32_t v, const rational_t *q);


/*
 * Find or add the record with key <tag, v, q>
 * - return the existing record if it exists in the table
 * - otherwise: create a new record with val = -1,
 *   add it to the table and return a pointer to the new record.
 * The caller must check val to determine whether the record is new
 * or not and set val to something else than -1.
 */
extern divmod_rec_t *divmod_table_get(divmod_tbl_t *tbl, divmod_tag_t tag, int32_t v, const rational_t *q);


/*
 * Special cases:
 * - floor x: tag = floor, var = x, q = one
 * - ceil x:  tag = ceil,  var = x, q = one 
 * - div x a: tag = floor or ceil, var = x, q = a
 *   For div, the tag is floor is a>0 and ceil if a<0.
 */
static inline divmod_rec_t *divmod_table_find_floor(divmod_tbl_t *tbl, int32_t x) {
  return divmod_table_find(tbl, DIVMOD_FLOOR_TAG, x, &tbl->one);
}

static inline divmod_rec_t *divmod_table_find_ceil(divmod_tbl_t *tbl, int32_t x) {
  return divmod_table_find(tbl, DIVMOD_CEIL_TAG, x, &tbl->one);
}

extern divmod_rec_t *divmod_table_find_div(divmod_tbl_t *tbl, int32_t x, const rational_t *a);


// same thing for get
static inline divmod_rec_t *divmod_table_get_floor(divmod_tbl_t *tbl, int32_t x) {
  return divmod_table_get(tbl, DIVMOD_FLOOR_TAG, x, &tbl->one);
}

static inline divmod_rec_t *divmod_table_get_ceil(divmod_tbl_t *tbl, int32_t x) {
  return divmod_table_get(tbl, DIVMOD_CEIL_TAG, x, &tbl->one);
}

extern divmod_rec_t *divmod_table_get_div(divmod_tbl_t *tbl, int32_t x, const rational_t *a);



#endif /* __DIVMOD_TABLE_H */
