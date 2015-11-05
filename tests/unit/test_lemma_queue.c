/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <assert.h>

#include "solvers/cdcl/smt_core.h"
#include "utils/memalloc.h"


/*
 * Code copied from smt_core.c
 */

/*
 * Initialize queue: nothing is allocated yet
 */
static void init_lemma_queue(lemma_queue_t *queue) {
  queue->capacity = 0;
  queue->nblocks = 0;
  queue->free_block = 0;
  queue->block = NULL;
}

/*
 * Delete all allocated blocks and the array queue->block
 */
static void delete_lemma_queue(lemma_queue_t *queue) {
  uint32_t i;

  for (i=0; i<queue->nblocks; i++) {
    safe_free(queue->block[i]);
  }
  safe_free(queue->block);
  queue->block = NULL;
}


/*
 * Increase capacity: increase the size of the block array
 */
static void increase_lemma_queue_capacity(lemma_queue_t *queue) {
  uint32_t  n;

  n = 2 * queue->capacity; // new capacity
  if (n == 0) {
    n = DEF_LEMMA_BLOCKS;
  }

  if (n >= MAX_LEMMA_BLOCKS) {
    out_of_memory();
  }

  queue->block = (lemma_block_t **) safe_realloc(queue->block, n * sizeof(lemma_block_t *));
  queue->capacity = n;
}


/*
 * Allocate a block of the given size
 */
static lemma_block_t *new_lemma_block(uint32_t size) {
  lemma_block_t *tmp;

  if (size >= MAX_LEMMA_BLOCK_SIZE) {
    out_of_memory();
  }

  tmp = (lemma_block_t *) safe_malloc(sizeof(lemma_block_t) + size * sizeof(literal_t));
  tmp->size = size;
  tmp->ptr = 0;

  return tmp;
}


/*
 * Find a block b that has space for n literals (i.e., b->size - b->ptr >= n)
 * - use the top_block if that works, otherwise use the next block
 * - allocate blocks if necessary
 */
static lemma_block_t *find_block_for_lemma(lemma_queue_t *queue, uint32_t n) {
  uint32_t i, j;
  lemma_block_t *tmp;

  /*
   * invariants:
   * 0 <= free_block <= nblocks <= capacity
   * block has size = capacity
   * if 0 <= i < free_block-1 then block[i] is full
   * if free_block > 0, then block[free_block-1] is not empty and not full
   * if free_block <= i < nblocks then block[i] is allocated and empty
   * if nblocks <= i < capacity then block[i] is not allocated
   */
  i = queue->free_block;
  if (i > 0) {
    // try the current block
    tmp = queue->block[i-1];
    assert(tmp != NULL && tmp->ptr > 0);
    if (tmp->size - tmp->ptr >= n) return tmp;
  }

  // current block does not exist or it's full.
  // search for a large enough block among block[free_blocks ... nblocks-1]
  for (j=i; j<queue->nblocks; j++) {
    tmp = queue->block[j];
    assert(tmp != NULL && tmp->ptr == 0);
    if (tmp->size >= n) {
      // swap block[i] and block[j]
      queue->block[j] = queue->block[i];
      queue->block[i] = tmp;
      queue->free_block ++;
      return tmp;
    }
  }

  // we need to allocate a new block, large enough for n literals
  if (n < DEF_LEMMA_BLOCK_SIZE) {
    n = DEF_LEMMA_BLOCK_SIZE;
  }
  tmp = new_lemma_block(n);

  // make room in queue->block if necessary
  j = queue->nblocks;
  if (j >= queue->capacity) {
    increase_lemma_queue_capacity(queue);
    assert(queue->nblocks < queue->capacity);
  }

  queue->block[j] = queue->block[i];
  queue->block[i] = tmp;
  queue->free_block ++;
  queue->nblocks ++;

  return tmp;
}


/*
 * Push literal array a[0] ... a[n-1] as a lemma
 */
static void push_lemma(lemma_queue_t *queue, uint32_t n, literal_t *a) {
  lemma_block_t *blk;
  uint32_t i;
  literal_t *b;

  blk = find_block_for_lemma(queue, n+1);
  assert(queue->free_block > 0 && blk == queue->block[queue->free_block-1]
	 && blk->ptr + n < blk->size);

  b = blk->data + blk->ptr;
  for (i=0; i<n; i++) {
    b[i] = a[i];
  }
  b[i] = null_literal; // end-marker;
  i++;
  blk->ptr += i;
}


/*
 * Empty the queue
 */
static void reset_lemma_queue(lemma_queue_t *queue) {
  uint32_t i;

  for (i=0; i<queue->nblocks; i++) {
    queue->block[i]->ptr = 0;
  }
  queue->free_block = 0;
}





/*
 * Testing code starts here
 */
static lemma_queue_t qq;
static literal_t a[5] = { 1, 2, 3, 4, 5 };
static literal_t b[10] = { 101, 102, 103, 104, 105, 106, 107, 108, 109, 110 };
static literal_t c[2000];

/*
 * Print the content of the queue
 */
static void show_lemma_queue(lemma_queue_t *queue) {
  lemma_block_t *tmp;
  uint32_t i;

  printf("Queue %p\n", queue);
  printf("  capacity  = %"PRIu32"\n", queue->capacity);
  printf("  nblocks   = %"PRIu32"\n", queue->nblocks);
  printf("  free_block = %"PRIu32"\n", queue->free_block);
  for (i=0; i<queue->nblocks; i++) {
    tmp = queue->block[i];
    printf("  block[%"PRIu32"]->size = %"PRIu32"\n", i, tmp->size);
    printf("  block[%"PRIu32"]->ptr  = %"PRIu32"\n", i, tmp->ptr);
  }
  printf("\n");
}

/*
 * Print all the lemmas in queue
 */
static void print_lemmas(lemma_queue_t *queue) {
  lemma_block_t *tmp;
  uint32_t i, j, n;

  for (i=0; i<queue->free_block; i++) {
    tmp = queue->block[i];
    n = tmp->ptr; // last used element
    j = 0;
    do {
      printf("{");
      while (tmp->data[j] != null_literal) {
	printf(" %"PRId32, tmp->data[j]);
	j ++;
      }
      printf(" }\n");
      j ++;
    } while (j < n);
  }
}

int main(void) {
  uint32_t i;

  // initialize lemma c
  for (i=0; i<2000; i++) {
    c[i] = 1000 + i;
  }

  init_lemma_queue(&qq);
  printf("\n*** Initial ***\n");
  show_lemma_queue(&qq);
  printf("*** Lemmas ***\n");
  print_lemmas(&qq);

  push_lemma(&qq, 5, a);
  printf("\n*** Adding a (5 literals) ***\n");
  show_lemma_queue(&qq);
  printf("*** Lemmas ***\n");
  print_lemmas(&qq);


  push_lemma(&qq, 10, b);
  printf("\n*** Adding b (10 literals) ***\n");
  show_lemma_queue(&qq);
  printf("*** Lemmas ***\n");
  print_lemmas(&qq);

  push_lemma(&qq, 0, NULL);
  printf("\n*** Adding empty lemma ***\n");
  show_lemma_queue(&qq);
  printf("*** Lemmas ***\n");
  print_lemmas(&qq);

  push_lemma(&qq, 0, NULL);
  printf("\n*** Adding empty lemma ***\n");
  show_lemma_queue(&qq);
  printf("*** Lemmas ***\n");
  print_lemmas(&qq);

  push_lemma(&qq, 0, NULL);
  push_lemma(&qq, 0, NULL);
  push_lemma(&qq, 0, NULL);
  printf("\n*** Adding empty lemmas (3 times) ***\n");
  show_lemma_queue(&qq);
  printf("*** Lemmas ***\n");
  print_lemmas(&qq);

  for (i=0; i<200; i++) {
    push_lemma(&qq, 10, b);
  }
  printf("\n*** Adding 200 lemmas of 10 literals each ***\n");
  show_lemma_queue(&qq);
  printf("*** Lemmas ***\n");
  print_lemmas(&qq);

  push_lemma(&qq, 2000, c);
  printf("\n*** Adding large lemma (2000 literals) ***\n");
  show_lemma_queue(&qq);

  push_lemma(&qq, 10, b);
  printf("\n*** Adding lemma b (10 literals) ***\n");
  show_lemma_queue(&qq);

  reset_lemma_queue(&qq);
  printf("\n*** After reset ***\n");
  show_lemma_queue(&qq);
  printf("*** Lemmas ***\n");
  print_lemmas(&qq);

  push_lemma(&qq, 2000, c);
  printf("\n*** Adding large lemma (2000 literals) ***\n");
  show_lemma_queue(&qq);
  printf("*** Lemmas ***\n");
  print_lemmas(&qq);


  push_lemma(&qq, 10, b);
  printf("\n*** Adding b (10 literals) ***\n");
  show_lemma_queue(&qq);
  printf("*** Lemmas ***\n");
  print_lemmas(&qq);

  push_lemma(&qq, 5, a);
  printf("\n*** Adding a (5 literals) ***\n");
  show_lemma_queue(&qq);
  printf("*** Lemmas ***\n");
  print_lemmas(&qq);


  delete_lemma_queue(&qq);
  return 0;
}
