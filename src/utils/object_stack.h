/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
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
 * STACK OF OBJECTS WITH SUPPORT FOR CLEANUP
 */

#ifndef __OBJECT_STACK_H
#define __OBJECT_STACK_H

#include <stddef.h>

/*
 * This stack is intended to support allocation and deallocation
 * of regular object (with a limit on object size). This is to
 * avoid memory leak when processing is interrupted by a longjmp.
 *
 * Example form context.c:
 *
 *   flatten_ite_to_eterm(context_t *ctx ...) {
 *      ite_flattener_t flattener;
 *      ...
 *      init_ite_flattener(&flattener);
 *      <do stuff that may call longjmp>
 *      delete_ite_flattener(&flattener);
 *      return ...
 *   }
 *
 * We have a memory leak if the longjmp is calleed because delete_ite_flattener is not
 * called in this case.
 *
 * This stack is intended to fix this issue. The previous code should be rewritten
 * as follows:
 *
 *   flatten_ite_to_eterm(contex_t *ctx ...) {
 *      ite_flattener_t *flattener;
 *      ...
 *      flattener = objstack_alloc(ctx->aux_stack, sizeof(ite_flattener_t), delete_ite_flattener);
 *      <do stufff that may call longjmp>
 *      objstack_pop(ctx->aux_stack);
 *      return
 *   }
 *
 * If a longjmp is called, the code that processes the exception
 * must call reset_objsatck(ctx->aux_stack) to free all objects.
 */


/*
 * Implementation
 * - the stack is a list of blocks of fixed size
 * - the last block in the list is where objects are allocated
 * - all previous blocks are full.
 *
 * In a block, an object of size n (in bytes) starts at some address p.
 * Before the object we store medata:
 *     size = n
 *     cleaner = pointer for a function that will free the object.
 *
 * Object sizes are rounded up to the next multiple of 16.
 */

/*
 * Cleaner function: takes a single pointer argument (to the object to be cleaned)
 */
typedef void (*cleaner_t)(void *);

/*
 * Meta data for an object
 */
typedef struct objstack_meta_s {
  size_t size;
  cleaner_t cleaner;
} objstack_meta_t;


/*
 * Block structure:
 * - a header + an array of BLOCKSIZE bytes
 * - the header keeps track of the space available in
 *   the block and has a pointer to a successor block.
 * - objects are allocated in a block starting at the end
 *
 * So for a full block b:
 * b->next = successor of b (or NULL)
 * b->leftover = number of unused bytes in b
 * b->data + b->leftover: start of the used bytes
 * b->data + BLOCK_SIZE: end of the used bytes
 *
 * The array b->data[left-over, ..., BLOCK_SIZE -1]
 * is split into segments each containing the metadata
 * for an object followed by the object itself.
 */
typedef struct objstack_block_s objstack_block_t;

typedef struct objstack_block_header_s {
  objstack_block_t *next;
  size_t leftover;
} objstack_block_header_t;

#define OBJSTACK_FULL_SIZE ((size_t)16384)
#define OBJSTACK_BLOCK_SIZE (OBJSTACK_FULL_SIZE - sizeof(objstack_block_header_t))

struct objstack_block_s {
  objstack_block_header_t h;
  char data[OBJSTACK_BLOCK_SIZE];
};


/*
 * Largest object size that's supported
 * - that's OBJSTACK_BLOCKS_SIZE - size of the metadata rounded up to a multiple of 16
 */
#define MAX_OBJSTACK_SIZE (OBJSTACK_BLOCK_SIZE - (((sizeof(objstack_meta_t)+15)>>4)<<4))


/*
 * Stack:
 * - pointer to the last/current block
 * - number of bytes available in the current block
 * - a list of free blocks
 */
typedef struct objstack_s {
  objstack_block_t *current;
  size_t available;
  objstack_block_t *free;
} objstack_t;


/*
 * Initialize the stack. Nothing is allocated yet.
 */
extern void init_objstack(objstack_t *stack);

/*
 * Reset: call the cleaner function on all allocated objects
 * then empty the stack.
 */
extern void reset_objstack(objstack_t *stack);

/*
 * Delete: reset then delete all blocks in the free list
 */
extern void delete_objstack(objstack_t *stack);

/*
 * Allocate an object of size n
 * - n must be no more than MAX_OBJSTACK_SIZE
 * - f = the cleaner functio for this object (or NULL if no cleaner needed).
 */
extern void *objstack_alloc(objstack_t *stack, size_t n, cleaner_t f);

/*
 * Cleanup and free the last allocated object
 */
extern void objstack_pop(objstack_t *stack);


#endif /* __OBJECT_STACK_H */
