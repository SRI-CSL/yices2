/*
 * Exponentiation of integers
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
