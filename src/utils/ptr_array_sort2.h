/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SORT AN ARRAY OF POINTERS WITH A USER-SUPPLIED ORDERING
 */

#ifndef __PTR_ARRAY_SORT2_H
#define __PTR_ARRAY_SORT2_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Comparison function:
 * - the function is called as cmp(data, x, y) where
 *   data is a parameter given to the sort function
 *   x and y are two pointers in the array.
 * - cmp(data, x, y) must return true if x < y in the ordering.
 */
typedef bool (* ptr_cmp_fun_t)(void *data, void *x, void *y);


/*
 * Sort function:
 * - a = array of n pointers
 * - data = user data passed to the comparison function
 * - cmp = comparison function.
 */
extern void ptr_array_sort2(void **a, uint32_t n, void *data, ptr_cmp_fun_t cmp);


#endif /* __PTR_ARRAY_SORT2_H */
