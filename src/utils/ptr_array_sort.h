/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SORT OF POINTER ARRAYS
 */

#ifndef __PTR_ARRAY_SORT_H
#define __PTR_ARRAY_SORT_H

#include <stdint.h>

/*
 * Sort array a in increasing order
 * n = size of the array
 */
extern void ptr_array_sort(void **a, uint32_t n);

#endif /* __PTR_ARRAY_SORT_H */
