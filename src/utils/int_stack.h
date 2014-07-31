/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STACK FOR ALLOCATION OF INTEGER ARRAYS IN FIFO ORDER
 */

#ifndef __INT_STACK_H
#define __INT_STACK_H

#include <stdint.h>

/*
 * Memory blocks:
 * - array of integers + header
 * - header include: previous block on the stack (or NULL)
 * - size of the block
 * - index for allocation in that block
 */
typedef struct iblock_s iblock_t;

struct iblock_s {
  iblock_t *next;
  uint32_t size;
  uint32_t ptr;
  int32_t data[0]; // real size = size
};

#define DEFAULT_IBLOCK_SIZE 1024
#define MAX_IBLOCK_SIZE ((UINT32_MAX/4)-sizeof(iblock_t))

/*
 * Stack
 * 1) list of blocks
 * - current = head of the list = top block
 * 2) list of free blocks
 */
typedef struct {
  iblock_t *current;
  iblock_t *free;
} int_stack_t;


/*
 * Initialize
 */
extern void init_istack(int_stack_t *stack);

/*
 * Delete the full stack
 */
extern void delete_istack(int_stack_t *stack);

/*
 * Allocate an array of n integers
 */
extern int32_t *alloc_istack_array(int_stack_t *stack, uint32_t n);

/*
 * Free allocated array a
 * - a must be the last array allocated.
 */
extern void free_istack_array(int_stack_t *stack, int32_t *a);

/*
 * Reset: empty the stack
 */
extern void reset_istack(int_stack_t *stack);

#endif /* __INT_STACK_H */
