/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * EXPONENTIATION OF INTEGERS
 */

#ifndef __INT_POWERS_H
#define __INT_POWERS_H

#include <stdint.h>

/*
 * Return x^d (modulo 2^32 or 2^64)
 */
extern uint32_t upower32(uint32_t x, uint32_t d);
extern uint64_t upower64(uint64_t x, uint32_t d);

#endif /* __INT_POWERS_H */
