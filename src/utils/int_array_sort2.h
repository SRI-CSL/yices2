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
 * SORT AN ARRAY OF INTEGERS WITH A USER-SUPPLIED ORDERING
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
