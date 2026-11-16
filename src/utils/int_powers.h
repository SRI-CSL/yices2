/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * EXPONENTIATION OF INTEGERS
 */

#ifndef __INT_POWERS_H
#define __INT_POWERS_H

#include <stdbool.h>
#include <stdint.h>

/*
 * Return true iff N is a power of two.
 */
static inline bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
				   
/*
 * Return x^d (modulo 2^32 or 2^64)
 */
extern uint32_t upower32(uint32_t x, uint32_t d);
extern uint64_t upower64(uint64_t x, uint32_t d);

#endif /* __INT_POWERS_H */
