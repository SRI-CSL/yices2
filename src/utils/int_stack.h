/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
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
