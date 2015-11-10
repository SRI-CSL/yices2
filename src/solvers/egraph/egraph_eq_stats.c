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

#include <stdbool.h>
#include <stddef.h>
#include <inttypes.h>

#include "solvers/egraph/egraph_eq_stats.h"
#include "utils/memalloc.h"



/***********************
 *  RECORD ALLOCATION  *
 **********************/

/*
 * Initialize bank: don't allocate anything
 */
static void init_egeq_bank(egeq_bank_t *bank) {
  bank->capacity = 0;
  bank->nblocks = 0;
  bank->free_block = 0;
  bank->alloc_ptr = EGEQ_BLOCK_SIZE;
  bank->block = NULL;
}

/*
 * Delete bank
 */
static void delete_egeq_bank(egeq_bank_t *bank) {
  uint32_t i;

  for (i=0; i<bank->nblocks; i++) {
    safe_free(bank->block[i]);
  }
  safe_free(bank->block);
  bank->block = NULL;
}


/*
 * Reset
 */
static inline void reset_egeq_bank(egeq_bank_t *bank) {
  bank->free_block = 0;
  bank->alloc_ptr = EGEQ_BLOCK_SIZE;
}


/*
 * Increase the capacity by 50%
 */
static void extend_egeq_bank(egeq_bank_t *bank) {
  uint32_t n;

  n = bank->capacity;
  n += n>>1;
  if (n < DEF_EGEQ_BANK_SIZE) {
    n = DEF_EGEQ_BANK_SIZE;
  }
  if (n >= MAX_EGEQ_BANK_SIZE) out_of_memory();

  bank->block = (egeq_elem_t **) safe_realloc(bank->block, n * sizeof(egeq_elem_t *));
  bank->capacity = n;
}


/*
 * Allocate an new block
 */
static void allocate_egeq_block(egeq_bank_t *bank) {
  uint32_t i, n;

  i = bank->nblocks;
  n = bank->capacity;
  assert(i <= n);
  if (i == n) {
    extend_egeq_bank(bank);
    assert(i < bank->capacity);
  }
  bank->block[i] = (egeq_elem_t *) safe_malloc(EGEQ_BLOCK_SIZE * sizeof(egeq_elem_t));
  bank->nblocks = i+1;
}


/*
 * Allocate a new element
 */
static egeq_elem_t *alloc_egeq_elem(egeq_bank_t *bank) {
  uint32_t i, p;
  egeq_elem_t *tmp;

  i = bank->free_block;
  p = bank->alloc_ptr;
  assert(p <= EGEQ_BLOCK_SIZE);
  if (p == EGEQ_BLOCK_SIZE) {
    // the current block is full or does not exist
    if (i >= bank->nblocks) {
      allocate_egeq_block(bank);
      assert(i < bank->nblocks);
    }
    i ++;
    bank->free_block = i;
    p = 0;
  }
  assert(i > 0 && bank->block[i-1] != NULL);
  tmp = bank->block[i-1] + p;
  bank->alloc_ptr = p+1;

  return tmp;
}





/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * Initialize the stack: no memory allocated yet
 */
static void init_egeq_stack(egeq_levstack_t *stack) {
  stack->current_level = 0;
  stack->top_level = 0;
  stack->nmarks = 0;
  stack->size = 0;
  stack->data = NULL;
}


/*
 * Delete the stack
 */
static void delete_egeq_stack(egeq_levstack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty stack
 */
static void reset_egeq_stack(egeq_levstack_t *stack) {
  stack->current_level = 0;
  stack->top_level = 0;
  stack->nmarks = 0;
}


/*
 * Push mark <b, p> on top of the stack
 * - current_level must be larger than top_level
 */
static void push_egeq_mark(egeq_levstack_t *stack, uint32_t b, uint32_t p) {
  uint32_t i, k, n;

  assert(stack->current_level > stack->top_level);

  k = stack->current_level;
  i = stack->nmarks;
  n = stack->size;

  if (i == n) {
    // increase the size
    if (n < DEF_EGEQ_STACK_SIZE) {
      n = DEF_EGEQ_STACK_SIZE;
    } else {
      n += n>>1;
      if (n > MAX_EGEQ_STACK_SIZE) out_of_memory();
    }
    stack->data = (egeq_mark_t *) safe_realloc(stack->data, n * sizeof(egeq_mark_t));
    stack->size = n;
  }

  assert(i < n);
  stack->data[i].level = k;
  stack->data[i].blk_id = b;
  stack->data[i].index = p;

  stack->nmarks = i + 1;
  stack->top_level = k;
}



/*
 * Remove the top mark
 */
static void pop_top_mark(egeq_levstack_t *stack) {
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
 * Initialize to the default size
 */
static void init_egeq_htbl(egeq_htbl_t *table) {
  uint32_t i, n;
  egeq_elem_t **tmp;

  n = DEF_EGEQ_HTBL_SIZE;
  assert(n < MAX_EGEQ_HTBL_SIZE);

  tmp = (egeq_elem_t **) safe_malloc(n * sizeof(egeq_elem_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  table->data = tmp;
  table->size = n;
  table->nelems = 0;
  table->ndeleted = 0;

  table->resize_threshold = (uint32_t) (n * EGEQ_HTBL_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t) (n * EGEQ_HTBL_CLEANUP_RATIO);
}


/*
 * Delete table
 */
static void delete_egeq_htbl(egeq_htbl_t *table) {
  safe_free(table->data);
  table->data = NULL;
}


/*
 * Reset: empty the table
 */
static void reset_egeq_htbl(egeq_htbl_t *table) {
  uint32_t i, n;

  n = table->size;
  for (i=0; i<n; i++) {
    table->data[i] = NULL;
  }
  table->nelems = 0;
  table->ndeleted = 0;
}


/*
 * Store pointer e into a clean array data
 * - mask = size of data - 1 (size must be a power of 2)
 * - e->hash must be set to the correct hash code
 * - data must not be full and must not contain deleted marks
 */
static void egeq_htbl_clean_copy(egeq_elem_t **data, egeq_elem_t *e, uint32_t mask) {
  uint32_t j;

  j = e->hash & mask;
  while (data[j] != NULL) {
    j ++;
    j &= mask;
  }
  data[j] = e;
}


/*
 * Check whether pointer e is not NULL or DELETED_EG_ELEM
 * - HACK: we rely on ((uintptr_t) NULL) == 0 and
 *  ((uintptr_t) DELETED_EG_ELEM) == 1
 */
static inline bool live_element(egeq_elem_t *e) {
  return (((uintptr_t) e) >> 1) != 0;
}


/*
 * Remove all deleted element from table
 */
static void egeq_htbl_cleanup(egeq_htbl_t *table) {
  egeq_elem_t **tmp, *e;
  uint32_t i, n, mask;

  n = table->size;
  tmp = (egeq_elem_t **) safe_malloc(n * sizeof(egeq_elem_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  mask = n-1;
  for (i=0; i<n; i++) {
    e = table->data[i];
    if (live_element(e)) {
      egeq_htbl_clean_copy(tmp, e, mask);
    }
  }

  safe_free(table->data);
  table->data = tmp;
  table->ndeleted = 0;
}


/*
 * Remove dead elements if the deletion threshold is reached
 */
static inline void egeq_htbl_cleanup_if_needed(egeq_htbl_t *table) {
  if (table->ndeleted > table->cleanup_threshold) {
    egeq_htbl_cleanup(table);
  }
}


/*
 * Double the table size and remove dead elements
 */
static void egeq_htbl_extend(egeq_htbl_t *table) {
  egeq_elem_t **tmp, *e;
  uint32_t i, n, new_size, mask;

  n = table->size;
  new_size = 2 * n;
  if (new_size >= MAX_EGEQ_HTBL_SIZE) out_of_memory();
  tmp = (egeq_elem_t **) safe_malloc(new_size * sizeof(egeq_elem_t *));
  for (i=0; i<new_size; i++) {
    tmp[i] = NULL;
  }

  mask = new_size - 1;
  for (i=0; i<n; i++) {
    e = table->data[i];
    if (live_element(e)) {
      egeq_htbl_clean_copy(tmp, e, mask);
    }
  }

  safe_free(table->data);
  table->data = tmp;
  table->ndeleted = 0;
  table->size = new_size;
  table->resize_threshold = (uint32_t)(new_size * EGEQ_HTBL_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t)(new_size * EGEQ_HTBL_CLEANUP_RATIO);
}


/*
 * Remove e from the table
 * - e must be present and e->hash must be valid
 */
static void egeq_htbl_remove(egeq_htbl_t *table, egeq_elem_t *e) {
  uint32_t mask, j;

  mask = table->size - 1;
  j = e->hash & mask;
  while (table->data[j] != e) {
    j ++;
    j &= mask;
  }
  table->data[j] = DELETED_EG_ELEM;
  table->nelems --;
  table->ndeleted ++;
}




/**********************
 *  EGEQ OPERATIONS  *
 *********************/

/*
 * Initialize
 */
void init_egeq(egeq_t *egeq) {
  init_egeq_htbl(&egeq->htbl);
  init_egeq_stack(&egeq->stack);
  init_egeq_bank(&egeq->bank);
}


/*
 * Delete everything
 */
void delete_egeq(egeq_t *egeq) {
  delete_egeq_bank(&egeq->bank);
  delete_egeq_stack(&egeq->stack);
  delete_egeq_htbl(&egeq->htbl);
}


/*
 * Empty the egeq
 */
void reset_egeq(egeq_t *egeq) {
  reset_egeq_htbl(&egeq->htbl);
  reset_egeq_stack(&egeq->stack);
  reset_egeq_bank(&egeq->bank);
}



/*
 * Remove from htbl all objects in the bank
 * allocated after the mark <b, i>
 * - b = free_block at the time push_egeq_mark was called
 * - i = alloc_ptr at the time push_egeq_mark was called
 */
static void remove_level(egeq_bank_t *bank, egeq_htbl_t *htbl, uint32_t b, uint32_t i) {
  uint32_t n, p;
  egeq_elem_t *blk;

  /*
   * n = current free_block
   * p = current alloc_ptr in block[n-1]
   */
  n = bank->free_block;
  p = bank->alloc_ptr;

  /*
   * restore free_block and alloc_ptr to what they where on
   * entry to the current level.
   */
  bank->free_block = b;
  bank->alloc_ptr = i;

  /*
   * We want to remove
   * elements from i to EGEQ_BLOCK_SIZE - 1 in block[b-1]
   * elements from 0 to EGEQ_CLOCK_SIZE - 1 in block[b] to block[n-2]
   * elements from 0 to p - 1 in block[n-1]
   */
  if (i == EGEQ_BLOCK_SIZE) {
    // either b=0 or there's nothing to delete in block[b-1]
    i = 0;
    b ++;
  }

  assert(b>0);
  while (b<n) {
    blk = bank->block[b - 1];
    while (i<EGEQ_BLOCK_SIZE) {
      egeq_htbl_remove(htbl, blk+i);
      i ++;
    }
    i = 0;
    b ++;
  }

  // last block
  assert(b == n);
  blk = bank->block[b - 1];
  while (i<p) {
    egeq_htbl_remove(htbl, blk+i);
    i ++;
  }
}


/*
 * Pop: delete all element created at the current level
 */
void egeq_pop(egeq_t *egeq) {
  egeq_levstack_t *stack;
  uint32_t i;

  stack = &egeq->stack;
  assert(stack->current_level > 0);

  if (stack->current_level == stack->top_level) {
    assert(stack->nmarks > 0);
    i = stack->nmarks - 1;
    assert(stack->data[i].level == stack->current_level);
    remove_level(&egeq->bank, &egeq->htbl, stack->data[i].blk_id, stack->data[i].index);
    egeq_htbl_cleanup_if_needed(&egeq->htbl);
    pop_top_mark(stack);
  }

  stack->current_level --;
}


/*
 * Hash code for key <x, y> (based on Jenkins's lookup3 code)
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

static uint32_t hash_key(int32_t x, int32_t y) {
  uint32_t a, b, c;

  a = ((uint32_t) x);
  b = ((uint32_t) y);
  c = 0xdeadbeef;
  final(a, b, c);

  return c;
}


/*
 * Check whether e has key <x, y>
 */
static inline bool elem_matches(egeq_elem_t *e, int32_t x, int32_t y) {
  return e->x[0] == x && e->x[1] == y;
}

/*
 * Search for a egeqd element of key <x, y>
 * - return NULL if it's not in the table
 */
egeq_elem_t *egeq_find(egeq_t *egeq, int32_t x, int32_t y) {
  egeq_htbl_t *htbl;
  uint32_t j, h, mask;
  egeq_elem_t *e;

  htbl = &egeq->htbl;
  assert(htbl->nelems + htbl->ndeleted < htbl->size);

  mask = htbl->size - 1;
  h = hash_key(x, y);
  j = h & mask;
  for (;;) {
    e = htbl->data[j];
    if (e == NULL || (e != DELETED_EG_ELEM && e->hash == h && elem_matches(e, x, y))) {
      return e;
    }
    j ++;
    j &= mask;
  }
}



/*
 * Add a mark to the stack if current_level>top_level
 */
static void push_mark_if_needed(egeq_levstack_t *stack, egeq_bank_t *bank) {
  if (stack->current_level > stack->top_level) {
    push_egeq_mark(stack, bank->free_block, bank->alloc_ptr);
  }
}


/*
 * Find or add a egeq element <x, y>
 * - if the element is new, then its counters are initialized to 0
 */
egeq_elem_t *egeq_get(egeq_t *egeq, int32_t x, int32_t y) {
  egeq_htbl_t *htbl;
  uint32_t k, j, h, mask;
  egeq_elem_t *e;

  htbl = &egeq->htbl;
  assert(htbl->nelems + htbl->ndeleted < htbl->size);

  mask = htbl->size - 1;
  h = hash_key(x, y);
  j = h & mask;
  for (;;) {
    e = htbl->data[j];
    if (e == NULL) goto add;
    if (e == DELETED_EG_ELEM) break;
    if (e->hash == h && elem_matches(e, x, y)) goto found;
    j ++;
    j &= mask;
  }

  // htbl->data[j] = where new descriptor can be added
  k = j;
  for (;;) {
    k ++;
    k &= mask;
    e = htbl->data[k];
    if (e == NULL) {
      htbl->ndeleted --;
      goto add;
    }
    if (e != DELETED_EG_ELEM && e->hash == h && elem_matches(e, x, y)) goto found;
  }

 add:
  push_mark_if_needed(&egeq->stack, &egeq->bank);

  e = alloc_egeq_elem(&egeq->bank);
  e->hash = h;
  e->x[0] = x;
  e->x[1] = y;
  e->ctr[0] = 0;
  e->ctr[1] = 0;
  e->ctr[2] = 0;
  e->ctr[3] = 0;
  e->ctr[4] = 0;

  htbl->data[j] = e;
  htbl->nelems ++;
  if (htbl->nelems + htbl->ndeleted > htbl->resize_threshold) {
    egeq_htbl_extend(htbl);
  }

 found:
  return e;
}



/*
 * Print the table
 */
static void print_egeq_record(FILE *f, egeq_elem_t *e) {
  fprintf(f, "[i!%"PRId32", i!%"PRId32"]: %"PRIu32" %"PRIu32" %"PRIu32" %"PRIu32" %"PRIu32"\n",
          e->x[0], e->x[1], e->ctr[0], e->ctr[1], e->ctr[2], e->ctr[3], e->ctr[4]);
}

void print_egeq(FILE *f, egeq_t *egeq) {
  egeq_htbl_t *htbl;
  egeq_elem_t *r;
  uint32_t i, n;

  htbl = &egeq->htbl;
  n = htbl->size;
  for (i=0; i<n; i++) {
    r = htbl->data[i];
    if (live_element(r)) {
      print_egeq_record(f, r);
    }
  }
  fflush(stdout);
}
