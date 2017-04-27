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
 * BASIC SORT FOR INTEGER ARRAYS
 */

#ifndef __INT_ARRAY_SORT_H
#define __INT_ARRAY_SORT_H

#include <stdint.h>

/*
 * Sort array a in increasing order.
 * n = size of the array
 */
extern void int_array_sort(int32_t *a, uint32_t n);

#endif /* __INT_ARRAY_SORT_H */
