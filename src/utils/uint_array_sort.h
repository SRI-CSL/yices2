/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
