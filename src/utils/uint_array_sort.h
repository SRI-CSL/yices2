/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SORT INTEGER ARRAYS
 */

#ifndef __UINT_ARRAY_SORT_H
#define __UINT_ARRAY_SORT_H

#include <stdint.h>

/*
 * Sort array a in increasing order.
 * - n = size of the array
 * - this is the same as int_array_sort but for arrays of unsigned integers
 */
extern void uint_array_sort(uint32_t *a, uint32_t n);

#endif /* __UINT_ARRAY_SORT_H */
