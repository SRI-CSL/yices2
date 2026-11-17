/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
