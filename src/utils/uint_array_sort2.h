/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SORT AN ARRAY OF UNSIGNED INTEGERS WITH A USER-SUPPLIED ORDERING
 */

#ifndef __UINT_ARRAY_SORT2_H
#define __UINT_ARRAY_SORT2_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Comparison function:
 * - the function is called as cmp(data, x, y) where
 *   data is a parameter given to the sort function
 *   x and y are two integers in the array.
 * - cmp(data, x, y) must return true if x < y in the ordering.
 */
typedef bool (* uint_cmp_fun_t)(void *data, uint32_t x, uint32_t y);


/*
 * Sort function:
 * - a = array of n integers
 * - data = user data passed to the comparison function
 * - cmp = comparison function.
 */
extern void uint_array_sort2(uint32_t *a, uint32_t n, void *data, uint_cmp_fun_t cmp);


#endif /* __UINT_ARRAY_SORT2_H */
