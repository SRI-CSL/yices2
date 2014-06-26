/*
 * Sort for pointer arrays
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
