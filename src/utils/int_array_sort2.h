/*
 * Sort an array of integers with a user-supplied ordering
 */

#ifndef __INT_ARRAY_SORT2_H
#define __INT_ARRAY_SORT2_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Comparison function:
 * - the function is called as cmp(data, x, y) where
 *   data is a parameter given to the sort function
 *   x and y are two integers in the array.
 * - cmp(data, x, y) must return true if x < y in the ordering.
 */
typedef bool (* int_cmp_fun_t)(void *data, int32_t x, int32_t y);


/*
 * Sort function:
 * - a = array of n integers
 * - data = user data passed to the comparison function
 * - cmp = comparison function.
 */
extern void int_array_sort2(int32_t *a, uint32_t n, void *data, int_cmp_fun_t cmp);


#endif /* __INT_ARRAY_SORT2_H */
