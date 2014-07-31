/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STACK FOR ALLOCATION OF POINTER ARRAYS IN FIFO ORDER
 *
 * This is similar to int_stack but for arrays of (void*) pointers.
 */

#ifndef __PTR_STACK_H
#define __PTR_STACK_H

#include <stdint.h>

/*
 * Memory blocks:
 * - array of pointers + header
 * - header include: previous block on the stack (or NULL)
 * - size of the block
 * - index for allocation in that block
 */
typedef struct pblock_s pblock_t;

struct pblock_s {
  pblock_t *next;
  uint32_t size;
  uint32_t ptr;
  void *data[0]; // real size = size
};

#define DEFAULT_PBLOCK_SIZE 1024
#define MAX_PBLOCK_SIZE ((UINT32_MAX/8)-sizeof(pblock_t))


/*
 * Stack
 * 1) list of blocks
 * - current = head of the list = top block
 * 2) list of free blocks
 */
typedef struct {
  pblock_t *current;
  pblock_t *free;
} ptr_stack_t;


/*
 * Initialize
 */
extern void init_pstack(ptr_stack_t *stack);

/*
 * Delete the full stack
 */
extern void delete_pstack(ptr_stack_t *stack);

/*
 * Allocate an array of n pointers
 */
extern void **alloc_pstack_array(ptr_stack_t *stack, uint32_t n);

/*
 * Free allocated array a
 * - a must be the last array allocated.
 */
extern void free_pstack_array(ptr_stack_t *stack, void **a);

/*
 * Reset: empty the stack
 */
extern void reset_pstack(ptr_stack_t *stack);


#endif /* __PTR_STACK_H */
