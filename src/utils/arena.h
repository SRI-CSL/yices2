/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STACK-BASED MEMORY ALLOCATION
 */

#ifndef __ARENA_H
#define __ARENA_H

#ifdef ANDROID
#include <limits.h>
#else
#include <stddef.h>
#endif


/*
 * Memory block: array of char + header
 * header includes: pointer to the next block and size
 *
 * The offset  (block->data - block) should be a multiple of 8,
 * on both 32 and 64bit machines. Just in case, I've added
 * a padding array to the header. It can be fixed if necessary.
 */
typedef struct block_s block_t;

typedef struct block_header_s {
  block_t *next;
  size_t size;
} block_header_t;

struct block_s {
  union {
    block_header_t h;
    char padding[1]; // use to fix alignment if needed
  } p;
  char data[0]; // real size = size
};

/*
 * Mark for push/pop:
 * - block address + previous mark
 */
typedef struct arena_mark_s arena_mark_t;

struct arena_mark_s {
  block_t *blk;
  arena_mark_t *prev;
};

/*
 * Default and max block size
 */
#define DEFAULT_BLOCK_SIZE (4096-sizeof(block_t))
#define MAX_BLOCK_SIZE (SIZE_MAX/2)

/*
 * Arena:
 * 1) list of active blocks
 * - current_block = head of that list = block where memory is allocated
 * - index = allocation index in the current_block
 * 2) list of free blocks
 * 3) top mark (or null)
 */
typedef struct {
  block_t *current_block;
  size_t index;
  block_t *free_block;
  arena_mark_t *top_mark;
} arena_t;


/*
 * Initialize
 */
extern void init_arena(arena_t *a);

/*
 * Delete all blocks
 */
extern void delete_arena(arena_t *a);

/*
 * Put a mark
 */
extern void arena_push(arena_t *a);

/*
 * Free all objects allocated since the top mark
 */
extern void arena_pop(arena_t *a);

/*
 * Free all objects
 */
extern void arena_reset(arena_t *a);

/*
 * Allocate an object in arena a
 * - n = size of the object in bytes
 */
extern void *arena_alloc(arena_t *a, size_t n);


#endif /* __ARENA_H */
