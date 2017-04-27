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
