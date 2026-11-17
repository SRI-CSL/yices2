/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * GCD OF UNSIGNED INTEGERS
 */

#ifndef __GCD_H
#define __GCD_H

#include <stdint.h>

/*
 * gcd of two unsigned integers
 * both a and b must be positive.
 */
extern uint32_t gcd32(uint32_t a, uint32_t b);
extern uint64_t gcd64(uint64_t a, uint64_t b);

#endif /* __GCD_H */
