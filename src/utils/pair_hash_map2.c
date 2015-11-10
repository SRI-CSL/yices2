/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * HASH MAP2
 *
 * - map pairs of 32bit integers to 32bit integers
 * - supports push and pop.
 */

#include <stdbool.h>
#include <stddef.h>
#include <assert.h>

#include "utils/memalloc.h"
#include "utils/pair_hash_map2.h"



/*********************
 *  BANK OF TRIPLES  *
 ********************/

/*
 * Initialize bank: nothing allocated yet
 */
static void init_pmap2_bank(pmap2_bank_t *bank) {
  bank->capacity = 0;
  bank->nblocks = 0;
  bank->free_block = 0;
  bank->alloc_ptr = PMAP2_BLOCK_SIZE;
  bank->block = NULL;
}


/*
 * Free memory
 */
static void delete_pmap2_bank(pmap2_bank_t *bank) {
  uint32_t i;

  for (i=0; i<bank->nblocks; i++) {
    safe_free(bank->block[i]);
  }
  safe_free(bank->block);
  bank->block = NULL;
}


/*
 * Empty the bank
 */
static inline void reset_pmap2_bank(pmap2_bank_t *bank) {
  bank->free_block = 0;
  bank->alloc_ptr = PMAP2_BLOCK_SIZE;
}


/*
 * Allocate the initial block array or increase it by 50%
 */
static void extend_pmap2_bank(pmap2_bank_t *bank) {
  uint32_t n;

  n = bank->capacity;
  n += n>>1;
  if (n < PMAP2_DEF_BANK_SIZE) {
    n = PMAP2_DEF_BANK_SIZE;
  }
  if (n >= PMAP2_MAX_BANK_SIZE) {
    out_of_memory();
  }

  bank->block = (pmap2_rec_t **) safe_realloc(bank->block, n * sizeof(pmap2_rec_t *));
  bank->capacity = n;
}


/*
 * Allocate a new block and store it in the block array
 */
static void allocate_pmap2_block(pmap2_bank_t *bank) {
  uint32_t i;

  i = bank->nblocks;
  if (i == bank->capacity) {
    extend_pmap2_bank(bank);
  }
  assert(i < bank->capacity);
  bank->block[i] = (pmap2_rec_t *) safe_malloc(PMAP2_BLOCK_SIZE * sizeof(pmap2_rec_t));
  bank->nblocks = i+1;
}


/*
 * Allocate a new triple
 */
static pmap2_rec_t *alloc_pmap2_record(pmap2_bank_t *bank) {
  uint32_t i, p;
  pmap2_rec_t *tmp;

  i = bank->free_block;
  p = bank->alloc_ptr;
  if (p == PMAP2_BLOCK_SIZE) {
    // free_block is full or the bank is empty:
    // get a new block
    if (i == bank->nblocks) {
      allocate_pmap2_block(bank);
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
 * Initialize: no memory allocated yet
 */
static void init_pmap2_stack(pmap2_stack_t *stack) {
  stack->current_level = 0;
  stack->top_level = 0;
  stack->nmarks = 0;
  stack->size = 0;
  stack->data = NULL;
}

static void delete_pmap2_stack(pmap2_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty the stack
 */
static void reset_pmap2_stack(pmap2_stack_t *stack) {
  stack->current_level = 0;
  stack->top_level = 0;
  stack->nmarks = 0;
}


/*
 * Push mark <b, p> on top of the stack
 * - b = block index
 * - p = allocation index in block b
 * - current_level must be larger than top_level
 */
static void push_alloc_mark(pmap2_stack_t *stack, uint32_t b, uint32_t p) {
  uint32_t i, k, n;

  assert(stack->current_level > stack->top_level);

  k = stack->current_level;
  i = stack->nmarks;
  n = stack->size;

  if (i == n) {
    // allocate data array or make it larger by 50%
    if (n < PMAP2_DEF_STACK_SIZE) {
      n = PMAP2_DEF_STACK_SIZE;
      assert(n < PMAP2_MAX_STACK_SIZE);
    } else {
      n += n>>1;
      if (n >= PMAP2_MAX_STACK_SIZE) {
        out_of_memory();
      }
    }
    stack->data = (pmap2_mark_t *) safe_realloc(stack->data, n * sizeof(pmap2_mark_t));
    stack->size = n;
  }

  assert(i < n);
  stack->data[i].level = k;
  stack->data[i].block_id = b;
  stack->data[i].alloc_idx = p;

  stack->nmarks = i+1;
  stack->top_level = k;
}


/*
 * Remove the top mark
 */
static void pop_alloc_mark(pmap2_stack_t *stack) {
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
 * Initialize: use the default size
 */
static void init_pmap2_htbl(pmap2_htbl_t *table) {
  pmap2_rec_t **tmp;
  uint32_t i, n;

  n = PMAP2_DEF_HTBL_SIZE;
  assert(is_power_of_two(n) && n < PMAP2_MAX_HTBL_SIZE);

  tmp = (pmap2_rec_t **) safe_malloc(n * sizeof(pmap2_rec_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  table->data = tmp;
  table->size = n;
  table->nelems = 0;
  table->ndeleted = 0;

  table->resize_threshold = (uint32_t) (n * PMAP2_HTBL_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t) (n * PMAP2_HTBL_CLEANUP_RATIO);
}


static void delete_pmap2_htbl(pmap2_htbl_t *table) {
  safe_free(table->data);
  table->data = NULL;
}


/*
 * Empty the table: don't resize
 */
static void reset_pmap2_htbl(pmap2_htbl_t *table) {
  uint32_t i, n;

  n = table->size;
  for (i=0; i<n; i++) {
    table->data[i] = NULL;
  }
  table->nelems = 0;
  table->ndeleted = 0;
}


/*
 * Hash code for key (k0, k1) (based on Jenkin's lookup3 code)
 */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define final(a,b,c)      \
{                         \
  c ^= b; c -= rot(b,14); \
  a ^= c; a -= rot(c,11); \
  b ^= a; b -= rot(a,25); \
  c ^= b; c -= rot(b,16); \
  a ^= c; a -= rot(c,4);  \
  b ^= a; b -= rot(a,14); \
  c ^= b; c -= rot(b,24); \
}


static uint32_t pmap2_hash(int32_t k0, int32_t k1) {
  uint32_t a, b, c;

  a = (uint32_t) k0;
  b = (uint32_t) k1;
  c = 0x9341ad2a;
  final(a, b, c);

  return c;
}



/*
 * Store pointer e into clean array a:
 * - mask = size of a - 1 (the size of a must be a power of 2)
 * - a must not be full and must not contain deletion marks
 */
static void pmap2_htbl_clean_copy(pmap2_rec_t **a, pmap2_rec_t *e, uint32_t mask) {
  uint32_t j;

  j = pmap2_hash(e->k0, e->k1) & mask;
  while (a[j] != NULL) {
    j ++;
    j &= mask;
  }

  a[j] = e;
}


/*
 * Check whether pointer e is non NULL and different from
 * PMAP2_DELETED. (We use the fact that NULL = 0 and PMAP2_DELETED = 1.
 */
static inline bool live_record(pmap2_rec_t *e) {
  return (((uintptr_t) e) >> 1) != 0;
}


/*
 * Cleanup: remove all the deletion marks
 */
static void pmap2_htbl_cleanup(pmap2_htbl_t *table) {
  pmap2_rec_t **tmp;
  pmap2_rec_t *e;
  uint32_t i, n, mask;

  n = table->size;
  assert(is_power_of_two(n));

  tmp = (pmap2_rec_t **) safe_malloc(n * sizeof(pmap2_rec_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  mask = n - 1;
  for (i=0; i<n; i++) {
    e = table->data[i];
    if (live_record(e)) {
      pmap2_htbl_clean_copy(tmp, e, mask);
    }
  }

  safe_free(table->data);
  table->data = tmp;
  table->ndeleted = 0;
}



/*
 * Cleanup if the cleanup threshold is reached.
 * Do nothing otherwise.
 */
static inline void pmap2_htbl_cleanup_if_needed(pmap2_htbl_t *table) {
  if (table->ndeleted > table->cleanup_threshold) {
    pmap2_htbl_cleanup(table);
  }
}


/*
 * Double the size and remove the deletion marks
 */
static void pmap2_htbl_extend(pmap2_htbl_t *table) {
  pmap2_rec_t **tmp;
  pmap2_rec_t *e;
  uint32_t i, n, new_size, mask;

  n = table->size;
  new_size = 2 * n;
  if (new_size >= PMAP2_MAX_HTBL_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(new_size));

  tmp = (pmap2_rec_t **) safe_malloc(new_size * sizeof(pmap2_rec_t *));
  for (i=0; i<new_size; i++) {
    tmp[i] = NULL;
  }

  mask = new_size - 1;
  for (i=0; i<n; i++) {
    e = table->data[i];
    if (live_record(e)) {
      pmap2_htbl_clean_copy(tmp, e, mask);
    }
  }

  safe_free(table->data);
  table->data = tmp;
  table->ndeleted = 0;
  table->size = new_size;
  table->resize_threshold = (uint32_t) (new_size * PMAP2_HTBL_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t) (new_size * PMAP2_HTBL_CLEANUP_RATIO);
}


/*
 * Remove e from the table.
 * - e must be present
 */
static void pmap2_htbl_remove(pmap2_htbl_t *table, pmap2_rec_t *e) {
  uint32_t mask, j;

  assert(is_power_of_two(table->size));

  mask = table->size - 1;
  j = pmap2_hash(e->k0, e->k1) & mask;
  while (table->data[j] != e) {
    j ++;
    j &= mask;
  }

  table->data[j] = PMAP2_DELETED;
  table->nelems --;
  table->ndeleted ++;
}




/**************
 *  FULL MAP  *
 *************/

/*
 * Initialize everything
 */
void init_pmap2(pmap2_t *pmap) {
  init_pmap2_htbl(&pmap->htbl);
  init_pmap2_stack(&pmap->stack);
  init_pmap2_bank(&pmap->bank);
}


/*
 * Delete everything
 */
void delete_pmap2(pmap2_t *pmap) {
  delete_pmap2_htbl(&pmap->htbl);
  delete_pmap2_stack(&pmap->stack);
  delete_pmap2_bank(&pmap->bank);
}


/*
 * Empty the table and set current level to 0
 */
void reset_pmap2(pmap2_t *pmap) {
  reset_pmap2_htbl(&pmap->htbl);
  reset_pmap2_stack(&pmap->stack);
  reset_pmap2_bank(&pmap->bank);
}



/*
 * Remove from htbl all the records allocated after the mark b, i
 * - b = block index = free_block at the time push was called
 * - i = index in block = alloc_ptr at the time push was called
 */
static void remove_level(pmap2_bank_t *bank, pmap2_htbl_t *htbl, uint32_t b, uint32_t i) {
  uint32_t n, p;
  pmap2_rec_t *blk;

  /*
   * n = current free_block
   * p = current alloc_ptr
   */
  n = bank->free_block;
  p = bank->alloc_ptr;

  /*
   * Restore free_block and alloc_ptr
   */
  bank->free_block = b;
  bank->alloc_ptr = i;


  /*
   * Records to remove:
   * - in block b-1: all records from i to BLOCK_SIZE -1
   * - in blocks b to n-2: all records (from 0 to BLOCK_SIZE - 1)
   * - in block n-1: all records from 0 to p-1
   */
  if (i == PMAP2_BLOCK_SIZE) {
    // either b = 0 or nothing to delete in block b-1
    i = 0;
    b ++;
  }

  assert(b > 0);

  while (b < n) {
    blk = bank->block[b - 1];
    while (i < PMAP2_BLOCK_SIZE) {
      pmap2_htbl_remove(htbl, blk + i);
      i ++;
    }
    i = 0;
    b ++;
  }

  // last block:
  assert(b == n && b > 0);
  blk = bank->block[b - 1];
  while (i < p) {
    pmap2_htbl_remove(htbl, blk + i);
    i ++;
  }
}


/*
 * Pop: remove all records allocated at the current level
 * - current level must be positive
 */
void pmap2_pop(pmap2_t *pmap) {
  pmap2_stack_t *stack;
  uint32_t i;

  stack = &pmap->stack;
  assert(stack->current_level > 0 && stack->current_level >= stack->top_level);

  if (stack->current_level == stack->top_level) {
    assert(stack->nmarks > 0);
    i = stack->nmarks - 1;
    assert(stack->data[i].level == stack->current_level);
    remove_level(&pmap->bank, &pmap->htbl, stack->data[i].block_id, stack->data[i].alloc_idx);
    pmap2_htbl_cleanup_if_needed(&pmap->htbl);
    pop_alloc_mark(stack);
  }

  stack->current_level --;

  assert(stack->current_level >= stack->top_level);
}



/*
 * Search for record of key <k0, k1>
 * - return NULL if there's no matching record
 */
pmap2_rec_t *pmap2_find(pmap2_t *pmap, int32_t k0, int32_t k1) {
  pmap2_htbl_t *htbl;
  pmap2_rec_t *e;
  uint32_t i, mask;

  htbl = &pmap->htbl;
  assert(htbl->nelems + htbl->ndeleted < htbl->size); // otherwise the function loops

  assert(is_power_of_two(htbl->size));
  mask = htbl->size -1;

  i = pmap2_hash(k0, k1) & mask;
  for (;;) {
    e = htbl->data[i];
    if (e == NULL || (e != PMAP2_DELETED && e->k0 == k0 && e->k1 == k1)) {
      return e;
    }
    i ++;
    i &= mask;
  }
}



/*
 * Push the current (free_block + alloc_ptr) onto the stack if current_level > top_level
 */
static inline void push_alloc_mark_if_needed(pmap2_stack_t *stack, pmap2_bank_t *bank) {
  if (stack->current_level > stack->top_level) {
    push_alloc_mark(stack, bank->free_block, bank->alloc_ptr);
  }
}


/*
 * Find or add a record with key <k0, k1>
 * - if a new record is created, set its value to -1
 */
pmap2_rec_t *pmap2_get(pmap2_t *pmap, int32_t k0, int32_t k1) {
  pmap2_htbl_t *htbl;
  pmap2_rec_t *e;
  uint32_t i, j, mask;

  htbl = &pmap->htbl;
  assert(htbl->nelems + htbl->ndeleted < htbl->size);

  assert(is_power_of_two(htbl->size));
  mask = htbl->size - 1;

  i = pmap2_hash(k0, k1) & mask;
  for (;;) {
    e = htbl->data[i];
    if (e == NULL) goto add;
    if (e == PMAP2_DELETED) break;
    if (e->k0 == k0 && e->k1 == k1) goto found;
    i ++;
    i &= mask;
  }

  // i = index where new record can be added
  assert(htbl->data[i] == PMAP2_DELETED);

  j = i;
  for (;;) {
    j ++;
    j &= mask;
    e = htbl->data[j];
    if (e == NULL) {
      htbl->ndeleted --;
      goto add;
    }
    if (e != PMAP2_DELETED && e->k0 == k0 && e->k1 == k1) goto found;
  }

 add:
  /*
   * Create a new record and store it in htbl->data[i].
   */
  push_alloc_mark_if_needed(&pmap->stack, &pmap->bank);

  e = alloc_pmap2_record(&pmap->bank);
  e->k0 = k0;
  e->k1 = k1;
  e->val = -1;
  htbl->data[i] = e;

  htbl->nelems ++;
  if (htbl->nelems + htbl->ndeleted > htbl->resize_threshold) {
    pmap2_htbl_extend(htbl);
  }

 found:
  assert(e->k0 == k0 && e->k1 == k1);
  return e;
}




/*
 * ITERATOR
 * - call f(aux, p) for every p in the table
 */
void pmap2_iterate(pmap2_t *pmap, void *aux, pmap2_iterator_t f) {
  pmap2_htbl_t *htbl;
  pmap2_rec_t *p;
  uint32_t i, n;

  htbl = &pmap->htbl;
  n = htbl->size;
  for (i=0; i<n; i++) {
    p = htbl->data[i];
    if (live_record(p)) {
      f(aux, p);
    }
  }
}
