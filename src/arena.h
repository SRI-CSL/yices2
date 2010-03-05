/*
 * Stack-based memory allocation
 * (TODO: check the cost of empty pushes. They can be optimized away)
 */

#ifndef __ARENA_H
#define __ARENA_H

#include <stddef.h>

/*
 * Memory block: array of char + header
 * header includes: pointer to the next block and size
 */
typedef struct block_s block_t;

struct block_s {
  block_t *next;
  size_t size;
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
#define DEFAULT_BLOCK_SIZE 4096
#define MAX_BLOCK_SIZE (SIZE_MAX/2)

/*
 * Arena:
 * 1) list of active blocks
 * - current_block = head of that list = block where memory is allocated 
 * - index = allocation index in current_block
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
