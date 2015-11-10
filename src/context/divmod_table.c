/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Table for internalization of div/mod/floor/ceil
 */

#include <stdbool.h>
#include <stddef.h>
#include <assert.h>

#include "utils/hash_functions.h"
#include "utils/memalloc.h"
#include "context/divmod_table.h"


/*************
 *  BLOCKS   *
 ************/

/*
 * Initialize all rationals in block b
 */
static void init_divmod_block(divmod_rec_t *d) {
  uint32_t i, n;

  n = DIVMOD_BLOCK_SIZE;
  for (i=0; i<n; i++) {
    q_init(&d[i].q);
  }
}


/*
 * Delete all rationals in block b
 */
static void cleanup_divmod_block(divmod_rec_t *d) {
  uint32_t i, n;

  n = DIVMOD_BLOCK_SIZE;
  for (i=0; i<n; i++) {
    q_clear(&d[i].q);
  }
}



/**********
 *  BANK  *
 *********/

/*
 * Initialize: nothing allocated yet
 */
static void init_divmod_bank(divmod_bank_t *bank) {
  bank->capacity = 0;
  bank->nblocks = 0;
  bank->free_block = 0;
  bank->alloc_ptr = DIVMOD_BLOCK_SIZE;
  bank->block = NULL;
}


/*
 * Free memory
 */
static void delete_divmod_bank(divmod_bank_t *bank) {
  uint32_t i, n;

  n = bank->nblocks;
  for (i=0; i<n; i++) {
    cleanup_divmod_block(bank->block[i]);
    safe_free(bank->block[i]);
  }
  safe_free(bank->block);
  bank->block = NULL;
}


/*
 * Empty the bank
 */
static void reset_divmod_bank(divmod_bank_t *bank) {
  uint32_t i, n;

  n = bank->nblocks;
  for (i=0; i<n; i++) {
    cleanup_divmod_block(bank->block[i]);
  }
  bank->free_block = 0;
  bank->alloc_ptr = DIVMOD_BLOCK_SIZE;
}


/*
 * Allocate the initial array of blocks or make it larger by 50%
 */
static void extend_divmod_bank(divmod_bank_t *bank) {
  uint32_t n;

  n = bank->capacity;
  n += n>>1;
  if (n < DIVMOD_DEF_BANK_SIZE) {
    n = DIVMOD_DEF_BANK_SIZE;
  }
  if (n > DIVMOD_MAX_BANK_SIZE) {
    out_of_memory();
  }

  bank->block = (divmod_rec_t **) safe_realloc(bank->block, n * sizeof(divmod_rec_t *));
  bank->capacity = n;
}


/*
 * Allocate a new block and store it the block array
 */
static void alloc_divmod_block(divmod_bank_t *bank) {
  divmod_rec_t *b;
  uint32_t i;

  i = bank->nblocks;
  if (i == bank->capacity) {
    extend_divmod_bank(bank);
  }
  assert(i < bank->capacity);
  b = (divmod_rec_t *) safe_malloc(DIVMOD_BLOCK_SIZE * sizeof(divmod_rec_t));
  init_divmod_block(b);

  bank->block[i] = b;
  bank->nblocks = i + 1;
}


/*
 * Allocate a new record
 */
static divmod_rec_t *alloc_divmod_record(divmod_bank_t *bank) {
  divmod_rec_t *tmp;
  uint32_t i, p;

  i = bank->free_block;
  p = bank->alloc_ptr;
  if (p == DIVMOD_BLOCK_SIZE) {
    // the free block is full or the bank is empty
    // get a new block
    if (i == bank->nblocks) {
      alloc_divmod_block(bank);
    }
    assert(i < bank->nblocks);
    i ++;
    bank->free_block = i;
    p = 0;
  }

  // allocate element p in block i-1
  assert(0 < i && bank->block[i-1] != NULL);
  tmp = bank->block[i-1] + p;
  bank->alloc_ptr = p+1;

  return tmp;
}


/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * Initialize the stack. No memory allocated yet.
 */
static void init_divmod_stack(divmod_stack_t *stack) {
  stack->current_level = 0;
  stack->top_level = 0;
  stack->nmarks = 0;
  stack->size = 0;
  stack->data = NULL;
}

static void delete_divmod_stack(divmod_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty the stack
 */
static void reset_divmod_stack(divmod_stack_t *stack) {
  stack->current_level = 0;
  stack->top_level = 0;
  stack->nmarks = 0;
}


/*
 * Allocate the data array or make it larger by 50%
 */
static void extend_divmod_stack(divmod_stack_t *stack) {
  uint32_t n;

  n = stack->size;
  n += (n >> 1);
  if (n < DIVMOD_DEF_STACK_SIZE) {
    n = DIVMOD_DEF_STACK_SIZE;
  }
  if (n > DIVMOD_MAX_STACK_SIZE) {
    out_of_memory();
  }
  stack->data = (divmod_mark_t *) safe_realloc(stack->data, n * sizeof(divmod_mark_t));
  stack->size = n;
}

/*
 * Push <b, p> on top of the stack
 * - b = block index
 * - p = allocation index in block b
 * - current_level must be larger than top_level
 */
static void divmod_push_mark(divmod_stack_t *stack, uint32_t b, uint32_t p) {
  uint32_t i, k;

  assert(stack->current_level > stack->top_level);

  k = stack->current_level;
  i = stack->nmarks;

  if (i == stack->size) {
    extend_divmod_stack(stack);
  }
  assert(i < stack->size);

  stack->data[i].level = k;
  stack->data[i].block_id = b;
  stack->data[i].alloc_idx = p;

  stack->nmarks = i+1;
  stack->top_level = k;
}


/*
 * Remove the top mark
 */
static void divmod_pop_mark(divmod_stack_t *stack) {
  uint32_t i;

  assert(stack->nmarks > 0);

  i = stack->nmarks - 1;
  stack->nmarks = i;
  if (i == 0) {
    stack->top_level = 0;
  } else {
    stack->top_level = stack->data[i-1].level;
  }
}



/****************
 *  HASH TABLE  *
 ***************/

/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialize table: use the default size
 */
static void init_divmod_htbl(divmod_htbl_t *table) {
  divmod_rec_t **tmp;
  uint32_t i, n;

  n = DIVMOD_DEF_HTBL_SIZE;
  assert(is_power_of_two(n) && n < DIVMOD_MAX_HTBL_SIZE);

  tmp = (divmod_rec_t **) safe_malloc(n * sizeof(divmod_rec_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  table->data = tmp;
  table->size = n;
  table->nelems = 0;
  table->ndeleted = 0;

  table->resize_threshold = (uint32_t) (n * DIVMOD_HTBL_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t) (n * DIVMOD_HTBL_CLEANUP_RATIO);
}

/*
 * Free memory
 */
static void delete_divmod_htbl(divmod_htbl_t *table) {
  safe_free(table->data);
  table->data = NULL;
}

/*
 * Empty the table
 */
static void reset_divmod_htbl(divmod_htbl_t *table) {
  uint32_t i, n;

  n = table->size;
  for (i=0; i<n; i++) {
    table->data[i] = NULL;
  }
  table->nelems = 0;
  table->ndeleted = 0;
}


/*
 * Hash code for key (tag, var, rational)
 */
static uint32_t divmod_hash(divmod_tag_t tag, int32_t v, const rational_t *q) {
  uint32_t h_num, h_den;

  q_hash_decompose(q, &h_num, &h_den);
  return jenkins_hash_quad(h_num, tag, v, h_den, 0xade2ade4);
}


/*
 * Store pointer d into a clean array a
 * - mask = size of a - 1 (the size must be a power of 2)
 * - a must not be full
 */
static void divmod_htbl_clean_copy(divmod_rec_t **a, divmod_rec_t *d, uint32_t mask) {
  uint32_t i;

  i = divmod_hash(d->tag, d->var, &d->q) & mask;
  while (a[i] != NULL) {
    i ++;
    i &= mask;
  }

  a[i] = d;
}


/*
 * Check whether pointer d is live (not NULL and not DELETED)
 */
static inline bool divmod_live_record(divmod_rec_t *d) {
  // return d != NULL && d != DIVMOD_DELETED;
  return (((uintptr_t) d) >> 1) != 0;
}


/*
 * Cleanup the hash table: remove the deletion marks
 */
static void divmod_htbl_cleanup(divmod_htbl_t *table) {
  divmod_rec_t **tmp;
  divmod_rec_t *d;
  uint32_t i, n, mask;

  n = table->size;
  assert(is_power_of_two(n));

  tmp = (divmod_rec_t **) safe_malloc(n * sizeof(divmod_rec_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  mask = n - 1;
  for (i=0; i<n; i++) {
    d = table->data[i];
    if (divmod_live_record(d)) {
      divmod_htbl_clean_copy(tmp, d, mask);
    }
  }

  safe_free(table->data);
  table->data = tmp;
  table->ndeleted = 0;
}


/*
 * Cleanup if the threshold is reached.
 */
static inline void divmod_htbl_cleanup_if_needed(divmod_htbl_t *table) {
  if (table->ndeleted > table->cleanup_threshold) {
    divmod_htbl_cleanup(table);
  }
}


/*
 * Double the table size and remove deletion marks
 */
static void divmod_htbl_extend(divmod_htbl_t *table) {
  divmod_rec_t **tmp;
  divmod_rec_t *d;
  uint32_t i, n, new_size, mask;

  n = table->size;
  new_size = n << 1;
  if (new_size > DIVMOD_MAX_HTBL_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(new_size));

  tmp = (divmod_rec_t **) safe_malloc(new_size * sizeof(divmod_rec_t *));
  for (i=0; i<new_size; i++) {
    tmp[i] = NULL;
  }

  mask = new_size - 1;
  for (i=0; i<n; i++) {
    d = table->data[i];
    if (divmod_live_record(d)) {
      divmod_htbl_clean_copy(tmp, d, mask);
    }
  }

  safe_free(table->data);
  table->data = tmp;
  table->ndeleted = 0;
  table->size = new_size;
  table->resize_threshold = (uint32_t) (new_size * DIVMOD_HTBL_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t) (new_size * DIVMOD_HTBL_CLEANUP_RATIO);
}


/*
 * Remove record d from the table.
 * - d must be present
 */
static void divmod_htbl_remove(divmod_htbl_t *table, divmod_rec_t *d) {
  uint32_t mask, i;

  assert(is_power_of_two(table->size));

  mask = table->size - 1;
  i = divmod_hash(d->tag, d->var, &d->q) & mask;
  while (table->data[i] != d) {
    i ++;
    i &= mask;
  }

  table->data[i] = DIVMOD_DELETED;
  table->nelems --;
  table->ndeleted ++;
}


/****************
 *  FULL TABLE  *
 ***************/

/*
 * Initialization
 */
void init_divmod_table(divmod_tbl_t *tbl) {
  init_divmod_htbl(&tbl->htbl);
  init_divmod_stack(&tbl->stack);
  init_divmod_bank(&tbl->bank);
  q_init(&tbl->one);
  q_set_one(&tbl->one);
}

/*
 * Delete everything
 */
void delete_divmod_table(divmod_tbl_t *tbl) {
  delete_divmod_htbl(&tbl->htbl);
  delete_divmod_stack(&tbl->stack);
  delete_divmod_bank(&tbl->bank);
  q_clear(&tbl->one);
}

/*
 * Empty the table and reset current_level to 0
 */
void reset_divmod_table(divmod_tbl_t *tbl) {
  reset_divmod_htbl(&tbl->htbl);
  reset_divmod_stack(&tbl->stack);
  reset_divmod_bank(&tbl->bank);
}


/*
 * Remove from htbl all the records allocated after the mark b, i
 * - b = block index
 * - i = index in block b
 * restore free_block to b and alloc_ptr to i
 */
static void divmod_remove_level(divmod_bank_t *bank, divmod_htbl_t *htbl, uint32_t b, uint32_t i) {
  uint32_t n, p;
  divmod_rec_t *blk;

  n = bank->free_block;
  p = bank->alloc_ptr;

  // restore free_block and alloc_ptr
  bank->free_block = b;
  bank->alloc_ptr = i;

  /*
   * Records to remove:
   * - in block b-1: all records with index i to BLOCK_SIZE  - 1
   * - in blocks b to n-2: all the records 
   * - in block n-1: all records with index 0 to p-1
   */
  if (i == DIVMOD_BLOCK_SIZE) {
    // nothing to delete in block b-1 (or b=0)
    i = 0;
    b ++;
  }

  assert(b > 0);

  while (b < n) {
    blk = bank->block[b - 1];
    while (i < DIVMOD_BLOCK_SIZE) {
      divmod_htbl_remove(htbl, blk + i);
      i ++;
    }
    i = 0;
    b ++;
  }

  // last block
  assert(b == n && b > 0);
  blk = bank->block[b - 1];
  while (i < p) {
    divmod_htbl_remove(htbl, blk + i);
    i ++;
  }
}

/*
 * Pop: remove all records allocated at the current level
 * - the current level must be positive
 */
void divmod_table_pop(divmod_tbl_t *tbl) {
  divmod_stack_t *stack;
  uint32_t i;

  stack = &tbl->stack;
  assert(stack->current_level > 0 && stack->current_level >= stack->top_level);

  if (stack->current_level == stack->top_level) {
    assert(stack->nmarks > 0);
    i = stack->nmarks - 1;
    assert(stack->data[i].level == stack->current_level);
    divmod_remove_level(&tbl->bank, &tbl->htbl, stack->data[i].block_id, stack->data[i].alloc_idx);
    divmod_htbl_cleanup_if_needed(&tbl->htbl);
    divmod_pop_mark(stack);
  }

  stack->current_level --;

  assert(stack->current_level >= stack->top_level);
}


/*
 * Search for record with key <tag, v, q>
 * - return NULL if not in the table
 */
divmod_rec_t *divmod_table_find(divmod_tbl_t *tbl, divmod_tag_t tag, int32_t v, const rational_t *q) {
  divmod_htbl_t *htbl;
  divmod_rec_t *d;
  uint32_t i, mask;

  htbl = &tbl->htbl;
  assert(htbl->nelems + htbl->ndeleted < htbl->size);

  assert(is_power_of_two(htbl->size));
  mask = htbl->size - 1;

  i = divmod_hash(tag, v, q) & mask;
  for (;;) {
    d = htbl->data[i];
    if (d == NULL ||
	(d != DIVMOD_DELETED && d->tag == tag && d->var == v && q_eq(&d->q, q))) {
      return d;
    }
    i ++;
    i &= mask;
  }
}


/*
 * Push the current pair (free block, alloc_ptr) onto the stack if 
 * current level > top level.
 */
static inline void divmod_push_mark_if_needed(divmod_stack_t *stack, divmod_bank_t *bank) {
  if (stack->current_level > stack->top_level) {
    divmod_push_mark(stack, bank->free_block, bank->alloc_ptr);
  }
}


/*
 * Find or add a record with key <tag, v, q>
 * - if a new record is created, set its value to -1
 */
divmod_rec_t *divmod_table_get(divmod_tbl_t *tbl, divmod_tag_t tag, int32_t v, const rational_t *q) {
  divmod_htbl_t *htbl;
  divmod_rec_t *e;
  uint32_t i, j, mask;

  htbl = &tbl->htbl;
  assert(htbl->nelems + htbl->ndeleted < htbl->size);

  assert(is_power_of_two(htbl->size));
  mask = htbl->size - 1;

  i = divmod_hash(tag, v, q) & mask;
  for (;;) {
    e = htbl->data[i];
    if (e == NULL) goto add;
    if (e == DIVMOD_DELETED) break;
    if (e->tag == tag && e->var == v && q_eq(&e->q, q)) goto found;
    i ++;
    i &= mask;
  }

  // i = index where new record can be added
  assert(htbl->data[i] == DIVMOD_DELETED);

  j = i;
  for (;;) {
    j ++;
    j &= mask;
    e = htbl->data[j];
    if (e == NULL) {
      htbl->ndeleted --;
      goto add;
    }
    if (e != DIVMOD_DELETED && e->tag == tag 
	&& e->var == v && q_eq(&e->q, q)) goto found;
  }

 add:
  /*
   * Create a new record and store it in htbl->data[i].
   */
  divmod_push_mark_if_needed(&tbl->stack, &tbl->bank);

  e = alloc_divmod_record(&tbl->bank);
  e->tag = tag;
  e->var = v;
  q_set(&e->q, q);
  e->val = -1;
  htbl->data[i] = e;

  htbl->nelems ++;
  if (htbl->nelems + htbl->ndeleted > htbl->resize_threshold) {
    divmod_htbl_extend(htbl);
  }

 found:
  assert(e->tag == tag && e->var == v && q_eq(&e->q, q));
  return e;
}


/*
 * Search the record for (div x a)
 * key for (div x a) = (floor, x, a) if a > 0
 *                  or (ceil, x, a)  if a < 0
 */
divmod_rec_t *divmod_table_find_div(divmod_tbl_t *tbl, int32_t x, const rational_t *a) {
  divmod_tag_t tag;

  tag = q_is_pos(a) ? DIVMOD_FLOOR_TAG : DIVMOD_CEIL_TAG;
  return divmod_table_find(tbl, tag, x, a);
}

divmod_rec_t *divmod_table_get_div(divmod_tbl_t *tbl, int32_t x, const rational_t *a) {
  divmod_tag_t tag;

  tag = q_is_pos(a) ? DIVMOD_FLOOR_TAG : DIVMOD_CEIL_TAG;
  return divmod_table_get(tbl, tag, x, a);
}

