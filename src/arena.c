/*
 * Stack-based memory allocation 
 */

#include <assert.h>
#include <stdint.h>
#include <limits.h>

#include "memalloc.h"
#include "arena.h"

/*
 * Allocate a new block of size n
 */
static block_t *new_block(size_t n) {
  block_t *tmp;

  if (n >= MAX_BLOCK_SIZE) {
    out_of_memory();
  }
  tmp = (block_t *) safe_malloc(sizeof(block_t) + n);
  tmp->size = n;
  return tmp;
}

/*
 * Get a new block of DEFAULT_BLOCK_SIZE from the free list
 * or allocate a new one.
 */
static void alloc_block(arena_t *a) {
  block_t *blk;

  blk = a->free_block;
  if (blk != NULL) {
    a->free_block = blk->next;
  } else {
    blk = new_block(DEFAULT_BLOCK_SIZE);
  }

  // blk = new current block
  blk->next = a->current_block;
  a->current_block = blk;
  a->index = blk->size;
}

/*
 * Get a block of size n (n larger than DEFAULT_BLOCK_SIZE)
 */
static void alloc_big_block(arena_t *a, size_t n) {
  block_t *blk;

  blk = new_block(n);
  blk->next = a->current_block;
  a->current_block = blk;
  a->index = n;
}

/*
 * Recycle block
 */
static void free_block(arena_t *a, block_t *blk) {
  blk->next = a->free_block;
  a->free_block = blk;
}


/*
 * Initialize a
 */
void init_arena(arena_t *a) {
  a->current_block = NULL;
  a->index = 0;
  a->free_block = NULL;
  a->top_mark = NULL;
} 

/*
 * Delete a: free all blocks
 */
void delete_arena(arena_t *a) {
  block_t *blk, *next;

  blk = a->free_block;
  while (blk != NULL) {
    next = blk->next;
    safe_free(blk);
    blk = next;
  }

  blk = a->current_block;
  while (blk != NULL) {
    next = blk->next;
    safe_free(blk);
    blk = next;
  }
  a->free_block = NULL;
  a->current_block = NULL;
  a->top_mark = NULL;
}


/*
 * Round size_t to next multiple of 4 on 32bit machines,
 * or 8 on 64 bit machines.
 */
static inline size_t align_size(size_t n) {
#if (ULONG_MAX == 4294967295UL) 
  return (n + 3) & ~((size_t) 3);
#elif (ULONG_MAX == 18446744073709551615UL)
  return (n + 7) & ~((size_t) 7);
#else
#error Could not find pointer alignment
#endif  
}


/*
 * Allocate an object of size n
 */
void *arena_alloc(arena_t *a, size_t n) {
  size_t idx;

  n = align_size(n);
  idx = a->index;
  if (idx < n) {
    // need a new block
    if (n <= DEFAULT_BLOCK_SIZE) {
      alloc_block(a);
    } else {
      alloc_big_block(a, n);
    }
    idx = a->index;
    assert(idx >= n);
  }
  idx -= n;
  a->index = idx;
  return a->current_block->data + idx;
}


/*
 * Put a mark
 */
void arena_push(arena_t *a) {
  arena_mark_t *mrk;

  mrk = (arena_mark_t *) arena_alloc(a, sizeof(arena_mark_t));
  mrk->blk = a->current_block;
  mrk->prev = a->top_mark;
  a->top_mark = mrk;
}

/*
 * Pop: erase everything allocated since the previous push
 */
void arena_pop(arena_t *a) {
  arena_mark_t *mrk;
  block_t *blk, *next, *mark_blk;
  size_t n;

  mrk = a->top_mark;
  assert(mrk != NULL);

  mark_blk = mrk->blk;
  blk = a->current_block;
  while (blk != mark_blk) {
    next = blk->next;
    free_block(a, blk);
    blk = next;
  }

  a->current_block = blk;
  a->top_mark = mrk->prev;
  n = ((char *) mrk) - blk->data;
  a->index = n + sizeof(arena_mark_t);
}


/*
 * Reset: erase everything
 */
void arena_reset(arena_t *a) {
  block_t *blk, *next;

  blk = a->current_block;
  while (blk != NULL) {
    next = blk->next;
    free_block(a, blk);
    blk = next;
  }

  a->current_block = NULL;
  a->top_mark = NULL;
  a->index = 0;
}
